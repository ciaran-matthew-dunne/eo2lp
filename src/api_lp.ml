(* api_lp.ml
   LambdaPi interface layer *)

(* ================================================================
   Logging infrastructure
   ================================================================ *)

(* Log severity levels — Silent < Error < Warn < Info < Debug.
   Debug enables per-symbol elaboration/encoding detail. *)
type log_level = Silent | Error | Warn | Info | Debug

let log_level = ref Silent
let set_log_level l = log_level := l

(* For backward compat with encode.ml's ~debug:!verbose pattern *)
let verbose = ref false

let no_color = ref false

let log_level_of_string = function
  | "debug" -> Debug
  | "info"  -> Info
  | "warn"  -> Warn
  | "error" -> Error
  | s -> failwith (Printf.sprintf
      "Unknown log level: %s (expected debug, info, warn, error)" s)

let log_level_geq level =
  let to_int = function
    | Silent -> 0 | Error -> 1 | Warn -> 2 | Info -> 3 | Debug -> 4 in
  to_int !log_level >= to_int level

(* Centralized ANSI color — respects --no-color globally *)
let color code s =
  if !no_color then s
  else Printf.sprintf "\027[%sm%s\027[0m" code s

let red s    = color "31" s
let green s  = color "32" s
let yellow s = color "33" s
let cyan s   = color "36" s
let dim s    = color "2" s

(* Debug context: tracks what symbol/module is currently being encoded *)
let current_module = ref ""
let current_symbol = ref ""
let current_phase = ref ""
let set_current_module m = current_module := m
let set_current_symbol s = current_symbol := s
let set_current_phase p = current_phase := p
let get_current_context () =
  let parts = [!current_module; !current_symbol; !current_phase]
    |> List.filter (fun s -> s <> "")
  in
  String.concat ":" parts

(* Scoped phase: sets current_phase, restores on return *)
let with_phase phase f =
  let saved = !current_phase in
  current_phase := phase;
  Fun.protect ~finally:(fun () -> current_phase := saved) f

(* Severity-gated logging — all goes to stderr.
   Level check is done before formatting to avoid wasted allocations.
   When disabled, ifprintf discards the format args without allocating. *)
let log_at level color_fn fmt =
  if log_level_geq level then
    Printf.ksprintf (fun s ->
      Printf.eprintf "  %s %s\n%!"
        (color_fn (Printf.sprintf "[%s]" (get_current_context ()))) s
    ) fmt
  else
    Printf.ikfprintf (fun () -> ()) () fmt

let log_info  fmt = log_at Info cyan fmt
let log_warn  fmt = log_at Warn yellow fmt
let log_error fmt = log_at Error red fmt
let log_debug fmt = log_at Debug dim fmt

(* Format-based warn for LambdaPi printer terms — gated on warn level *)
let log_warn_pp callback =
  if log_level_geq Warn then begin
    Timed.(Core.Print.print_implicits := true);
    Timed.(Core.Print.do_not_qualify := true);
    callback (get_current_context ())
  end

(* Error formatting with context *)
let format_error msg =
  let ctx = get_current_context () in
  if ctx = "" then msg
  else Printf.sprintf "[%s] %s" ctx msg

let fail msg = failwith (format_error msg)
let failf fmt = Printf.ksprintf fail fmt

(* LambdaPi modules *)
module Term      = Core.Term
module Sign      = Core.Sign
module Sig_state = Core.Sig_state
module Print     = Core.Print
module Ctxt      = Core.Ctxt
module LibTerm   = Core.LibTerm
module Compile   = Handle.Compile
module Package   = Parsing.Package
module Library   = Common.Library
module Path      = Common.Path
module Pos       = Common.Pos

(* Types *)
type term = Term.term
type sym  = Term.sym
type var  = Term.var
type rule = Term.rule
type sign = Sign.t
type ctxt = Term.ctxt

(* Term constructors *)
let mk_Symb   = Term.mk_Symb
let mk_Vari   = Term.mk_Vari
let mk_Kind   = Term.mk_Kind
let mk_Type   = Term.mk_Type
let mk_Appl   = Term.mk_Appl
let mk_Prod   = Term.mk_Prod
let mk_Abst   = Term.mk_Abst
let mk_Plac   = Term.mk_Plac
let mk_Patt   = Term.mk_Patt
let add_args  = Term.add_args
let new_var   = Term.new_var
let bind_var  = Term.bind_var
let unbind    = Term.unbind
let base_name = Term.base_name

(* Contexts *)
let empty_ctxt : ctxt = []

let ctxt_add ctx v ty =
  (v, ty, None) :: ctx

let ctxt_to_prod = Ctxt.to_prod

let ctxt_to_abst ctx t =
  List.fold_left
    (fun acc (v, ty, _) -> mk_Abst (ty, bind_var v acc))
    t ctx

let ctxt_find ctx name =
  List.find_map
    (fun (v, _, _) ->
       if base_name v = name then Some v else None)
    ctx

(* ================================================================
   Generic term traversal combinators
   ================================================================ *)

(* Fold over all sub-terms (short-circuiting boolean predicate). *)
let rec term_exists f = function
  | t when f t -> true
  | Term.Appl (t1, t2) -> term_exists f t1 || term_exists f t2
  | Term.Abst (a, b) | Term.Prod (a, b) ->
    term_exists f a || term_exists f (snd (unbind b))
  | Term.LLet (a, t, b) ->
    term_exists f a || term_exists f t || term_exists f (snd (unbind b))
  | _ -> false

(* Map over a term, applying f at each node. f returns Some t' to replace,
   None to recurse into children. *)
let rec term_map f t =
  match f t with
  | Some t' -> t'
  | None ->
    match t with
    | Term.Appl (t1, t2) -> Term.mk_Appl (term_map f t1, term_map f t2)
    | Term.Abst (a, b) ->
      let v, body = unbind b in
      Term.mk_Abst (term_map f a, bind_var v (term_map f body))
    | Term.Prod (a, b) ->
      let v, body = unbind b in
      Term.mk_Prod (term_map f a, bind_var v (term_map f body))
    | Term.LLet (a, t, b) ->
      let v, body = unbind b in
      Term.mk_LLet (term_map f a, term_map f t, bind_var v (term_map f body))
    | t -> t

(* ================================================================
   Term predicates and transformations (built on combinators)
   ================================================================ *)

let has_unsolved_metas t =
  term_exists (function
    | Term.Meta (m, _) -> Option.is_none Timed.(!(m.Term.meta_value))
    | _ -> false) t

(* Replace unsolved metas with placeholders so LambdaPi can re-infer them *)
let metas_to_plac t =
  term_map (function
    | Term.Meta (m, _) when Option.is_none Timed.(!(m.Term.meta_value)) ->
      Some (mk_Plac false)
    | _ -> None) t

let has_plac t =
  term_exists (function Term.Plac _ -> true | _ -> false) t

(* Pseudo-symbol rendering as "_". Print.term's internal cleanup rejects
   Plac nodes, so placeholders are swapped for this symbol just before
   printing; lambdapi re-infers the wildcards when checking the output. *)
let wildcard_sym =
  Term.create_sym [] Term.Privat Term.Defin Term.Eager false
    (Pos.none "_") None Term.mk_Kind []

let plac_to_wildcard t =
  term_map (function
    | Term.Plac _ -> Some (Term.mk_Symb wildcard_sym)
    | _ -> None) t

(* Signature state *)
let current_sign : sign option ref = ref None
let current_deps  : Path.t list ref = ref []

let get_sign () =
  match !current_sign with
  | Some s -> s
  | None   -> failwith "LambdaPi signature not initialized"

let init_sign ?(deps = []) path =
  current_deps := deps;
  match Path.Map.find_opt path Timed.(!(Sign.loaded)) with
  | Some sign ->
    current_sign := Some sign;
    sign
  | None ->
    let sign = Sign.create path in
    Timed.(Sign.loaded :=
             Path.Map.add path sign !(Sign.loaded));
    current_sign := Some sign;
    sign

let reset_sign () =
  current_sign := None;
  current_deps := []

(* Symbol storage for printing *)
let symbol_types : (string, term) Hashtbl.t =
  Hashtbl.create 32
let symbol_defs : (string, term) Hashtbl.t =
  Hashtbl.create 32
let symbol_asserts : (string, term) Hashtbl.t =
  Hashtbl.create 32

let reset_symbol_storage () =
  Hashtbl.clear symbol_types;
  Hashtbl.clear symbol_defs;
  Hashtbl.clear symbol_asserts

(* Remove a sign from Sign.loaded to free memory after encoding a proof *)
let remove_sign path =
  Timed.(Sign.loaded := Path.Map.remove path !(Sign.loaded))

(* Check if a type is a Proof type *)
let is_proof_type ty =
  match ty with
  | Term.Appl (Term.Symb s, _) -> s.Term.sym_name = "Proof"
  | _ -> false

(* Check for Stdlib.Nat symbols *)
let contains_nat_symbol t =
  term_exists (function
    | Term.Symb s ->
      (match s.Term.sym_path with "Stdlib" :: "Nat" :: _ -> true | _ -> false)
    | _ -> false) t

(* Symbol lookup *)
let find_in sign name =
  try Some (Sign.find sign name)
  with Not_found -> None

let find_symbol name =
  find_in (get_sign ()) name

let is_excluded_stdlib_path = function
  | "Stdlib" :: "Nat" :: _ -> true
  | _ -> false

let is_stdlib_path = function
  | "Stdlib" :: _ -> true
  | _ -> false

let find_symbol_global name =
  let result = ref None in
  (* Prefer non-Stdlib over Stdlib when a name exists in multiple signatures. *)
  let result_is_stdlib = ref false in
  Path.Map.iter
    (fun path sign ->
       if not (is_excluded_stdlib_path path) then
         match find_in sign name with
         | Some s ->
            let is_std = is_stdlib_path path in
            (match !result with
             | None ->
               result := Some s;
               result_is_stdlib := is_std
             | Some _ ->
               (* Replace only when we'd improve from Stdlib -> non-Stdlib. *)
               if !result_is_stdlib && not is_std then begin
                 result := Some s;
                 result_is_stdlib := false
               end)
         | None -> ())
    Timed.(!(Sign.loaded));
  !result

(* Add symbol to signature *)
let add_symbol_to_sign
    ?(expo=Term.Public)
    ?(prop=Term.Const)
    ?(mstrat=Term.Eager)
    ?(impl=[])
    name ty
  =
  let sign = get_sign () in
  let sym =
    Sign.add_symbol sign expo prop mstrat false
      (Pos.none name) None ty impl
  in
  Hashtbl.replace symbol_types name ty;
  sym

let add_constant ?(impl=[]) name ty =
  add_symbol_to_sign ~prop:Term.Const ~impl name ty

(* Register a proof symbol (assume/step). Uses Kind for Sign registration
   (which requires meta/plac-free types) then sets the real type on the
   symbol afterward. This lets infer_type return the real type for
   downstream premise-list folding. *)
let add_proof_constant name ty =
  let sign = get_sign () in
  let sym =
    Sign.add_symbol sign
      Term.Public Term.Const Term.Eager false
      (Pos.none name) None mk_Kind []
  in
  Timed.(sym.Term.sym_type := ty);
  Hashtbl.replace symbol_types name ty;
  sym

let add_proof_definition name ty def =
  let sign = get_sign () in
  let sym =
    Sign.add_symbol sign
      Term.Public Term.Defin Term.Eager false
      (Pos.none name) None mk_Kind []
  in
  Timed.(sym.Term.sym_def := Some def);
  let ty_final = match ty with Some t -> t | None -> mk_Kind in
  Timed.(sym.Term.sym_type := ty_final);
  (* Store Kind for printing so the symbol line has no type annotation.
     The real type is checked via a separate assert line. *)
  Hashtbl.replace symbol_types name mk_Kind;
  (match ty with
   | Some t -> Hashtbl.replace symbol_asserts name t
   | None -> ());
  let def_for_print =
    if has_unsolved_metas def then metas_to_plac def else def in
  Hashtbl.replace symbol_defs name def_for_print;
  sym

let add_sequential ?(impl=[]) name ty =
  add_symbol_to_sign
    ~prop:Term.Defin ~mstrat:Term.Sequen ~impl name ty


let add_definition ?(impl=[]) ?(print_ty=true) name ty def =
  let sign = get_sign () in
  let ty_final = match ty with Some t -> t | None -> mk_Kind in
  let def_for_print =
    if contains_nat_symbol def then
      if has_plac def then def
      else metas_to_plac def
    else if has_unsolved_metas def then
      metas_to_plac def
    else
      def
  in
  let sym =
    Sign.add_symbol sign
      Term.Public Term.Defin Term.Eager false
      (Pos.none name) None ty_final impl
  in
  Timed.(sym.Term.sym_def := Some def);
  (* When print_ty is false, store Kind so the printer omits the type
     annotation, while the internal LP symbol keeps the real type for
     infer_noexn. *)
  Hashtbl.replace symbol_types name (if print_ty then ty_final else mk_Kind);
  Hashtbl.replace symbol_defs name def_for_print;
  sym

(* Compilation *)
let compile path =
  let run () = Compile.compile Sig_state.dummy path in
  if !verbose then run ()
  else begin
    flush_all ();
    let old_out = Unix.dup Unix.stdout in
    let old_err = Unix.dup Unix.stderr in
    let null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
    Unix.dup2 null Unix.stdout;
    Unix.dup2 null Unix.stderr;
    Unix.close null;
    Fun.protect ~finally:(fun () ->
      Unix.dup2 old_out Unix.stdout;
      Unix.dup2 old_err Unix.stderr;
      Unix.close old_out;
      Unix.close old_err)
      run
  end

let init_library () =
  Library.set_lib_root None

let apply_package_config =
  Package.apply_config

(* Printing helpers *)
let set_print_implicits b = Timed.(Print.print_implicits := b)
let set_print_domains   b = Timed.(Print.print_domains := b)
let set_do_not_qualify  b = Timed.(Print.do_not_qualify := b)

(* Check if term is τ {|eo::Type|} which should print as Set *)
let is_tau_eo_type = function
  | Term.Appl (Term.Symb tau_sym, Term.Symb eo_type_sym) ->
    tau_sym.Term.sym_name = "τ" &&
    eo_type_sym.Term.sym_name = "{|eo::Type|}"
  | _ -> false

(* Table mapping symbol names to their alias targets (LambdaPi terms).
   Populated by encode.ml when processing declare-consts. *)
let alias_table : (string, term) Hashtbl.t = Hashtbl.create 4

let register_alias name target = Hashtbl.replace alias_table name target

(* Reset all per-proof state to prevent memory leaks across many proofs *)
let reset_proof_state ?(sign_path=[]) () =
  Hashtbl.clear symbol_types;
  Hashtbl.clear symbol_defs;
  Hashtbl.clear alias_table;
  reset_sign ();
  if sign_path <> [] then remove_sign sign_path

(* Reduce aliased symbols using the alias table *)
let rec reduce_aliases t =
  term_map (function
    | Term.Symb s ->
      (match Hashtbl.find_opt alias_table s.Term.sym_name with
       | Some target -> Some (reduce_aliases target)
       | None -> None)
    | _ -> None) t

(* Custom term printer that simplifies τ {|eo::Type|} to Set
   and reduces literal type aliases *)
let print_term ppf t =
  let t = reduce_aliases t in
  let t = if has_unsolved_metas t then metas_to_plac t else t in
  let t = if has_plac t then plac_to_wildcard t else t in
  if is_tau_eo_type t then
    Format.fprintf ppf "Set"
  else
    Print.term ppf t


let strip_lp_escapes_re = Str.regexp "{|\\([^|]*\\)|}"
let strip_lp_escapes s =
  Str.global_replace strip_lp_escapes_re "\\1" s

(* Symbols whose printed return type text needs post-processing to add
   explicit @-prefixed implicits. Maps symbol name to a list of
   (relation_sym_name, impl_arg_text) pairs, e.g.,
   [("arith_mult_sign", [">", "T T"; "<", "T T"])] *)
let explicit_impl_replacements : (string, (string * string) list) Hashtbl.t =
  Hashtbl.create 4

(* Register that a symbol's printed return type should have specific
   relation symbols replaced with @-prefixed versions *)
let register_explicit_replacements sym_name replacements =
  Hashtbl.replace explicit_impl_replacements sym_name replacements

(* Apply @-prefix replacements to printed text.
   E.g., replace standalone ">" with "(@> T T)" *)
let apply_explicit_replacements sym_name text =
  match Hashtbl.find_opt explicit_impl_replacements sym_name with
  | None -> text
  | Some repls ->
    List.fold_left (fun acc (rel_name, impl_args) ->
      let replacement = Printf.sprintf "(@%s %s)" rel_name impl_args in
      (* Match the symbol preceded and followed by space, paren, or
         start/end of string. Use a simple string replacement for
         exact matches like " > " or " >)" *)
      let re = Str.regexp (Printf.sprintf "\\([( ]\\)%s\\([ )]\\)" (Str.quote rel_name)) in
      Str.global_replace re (Printf.sprintf "\\1%s\\2" replacement) acc
    ) text repls

(* Prelude *)
let prelude : sign option ref = ref None

let prelude_sig () =
  match !prelude with
  | Some s -> s
  | None   -> failwith "Prelude not initialized"

let init prelude_sign =
  prelude := Some prelude_sign

let reset () =
  prelude := None;
  reset_symbol_storage ()

let find name =
  match find_in (prelude_sig ()) name with
  | Some s -> s
  | None ->
    match find_symbol_global name with
    | Some s -> s
    | None ->
      failwith (Printf.sprintf "Symbol '%s' not found." name)

(* Name encoding *)

(* Names that clash with LambdaPi builtins and cannot be escaped with {|...|} *)
let lp_reserved = ["Set"; "TYPE"]

(* Names that can be escaped with {|...|} to avoid clashes *)
let lp_keywords = [
  "as"; "in"; "let"; "open"; "require"; "rule";
  "symbol"; "with"; "type"; "repeat";
  "off"; "on"; "assert"; "begin"; "end";
  "compute"; "print"; "debug"; "abort"; "admitted";
  "assume"; "apply"; "have"; "generalize";
  "constant"; "injective"; "commutative"; "associative";
  "left"; "right"; "protected"; "sequential";
  "infix"; "prefix"; "postfix"; "quantifier";
  "builtin"; "notation"; "opaque"; "private";
  "inductive"; "coerce_rule"; "unif_rule";
  "refine"; "focus"; "simplify"; "solve"; "why3";
  "fail"; "reflexivity"; "symmetry"; "rewrite"; "try";
  "proofterm"; "flag"; "prover"; "prover_timeout";
  "verbose"
]

(* Boolean lookup table for O(1) invalid-char detection *)
let invalid_char_tbl =
  let tbl = Bytes.make 256 '\000' in
  List.iter (fun c -> Bytes.set tbl (Char.code c) '\001') [
    '\t'; '\r'; '\n'; ' '; ':'; ','; ';'; '`';
    '('; ')'; '{'; '}'; '['; ']'; '"'; '.';
    '@'; '$'; '|'; '?'; '/'
  ];
  tbl

let is_invalid_char c = Bytes.get invalid_char_tbl (Char.code c) <> '\000'

(* Set-based keyword lookup for O(1) detection *)
module SSet = Set.Make(String)
let lp_keyword_set = SSet.of_list lp_keywords
let lp_reserved_set = SSet.of_list lp_reserved

let starts_with_sign s =
  String.length s >= 2
  && (s.[0] = '+' || s.[0] = '-')
  && match s.[1] with 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true | _ -> false

let esc s =
  (* Reserved names must be prefixed to avoid clash with LambdaPi builtins *)
  if SSet.mem s lp_reserved_set then "{|eo::" ^ s ^ "|}"
  else if String.exists is_invalid_char s
     || SSet.mem s lp_keyword_set
     || Option.is_some (int_of_string_opt s)
     || starts_with_sign s
  then "{|" ^ s ^ "|}"
  else s

(* Symbol lookup with dependencies *)
let find_in_deps name =
  List.find_map
    (fun dep_path ->
       Option.bind
         (Path.Map.find_opt dep_path Timed.(!(Sign.loaded)))
         (fun sign -> find_in sign name))
    !current_deps

let find_sym name =
  (* Try both unescaped and escaped versions of the name *)
  let names = [name; esc name] |> List.sort_uniq String.compare in
  let try_find n =
    match find_symbol n with
    | Some s -> Some s
    | None ->
      match find_in_deps n with
      | Some s -> Some s
      | None ->
        match find_in (prelude_sig ()) n with
        | Some s -> Some s
        | None -> find_symbol_global n
  in
  List.find_map try_find names

let get_sym name =
  match find_sym name with
  | Some s -> s
  | None ->
    failf "Symbol `%s` not found" name

(* Look up a symbol registered as a lambdapi builtin (e.g. "int_zero" → Z0).
   Uses the canonical symbol from sign_builtins so that lambdapi's printer
   recognizes integer/pos terms by physical equality (==). *)
let get_builtin name =
  let find_in_sign sign =
    Lplib.Extra.StrMap.find_opt name Timed.(!(sign.Sign.sign_builtins))
  in
  match find_in_sign (prelude_sig ()) with
  | Some s -> s
  | None ->
    (* Fall back: search all loaded signatures *)
    let found = ref None in
    Path.Map.iter (fun _ sign ->
      if !found = None then
        match find_in_sign sign with
        | Some s -> found := Some s
        | None -> ()
    ) Timed.(!(Sign.loaded));
    match !found with
    | Some s -> s
    | None -> failf "Builtin `%s` not found" name

(* Printing support *)
let rec unwrap_lambdas n t =
  if n <= 0 then t
  else match t with
    | Term.Abst (_, b) -> unwrap_lambdas (n-1) (snd (unbind b))
    | _ -> t

let rec extract_params ty impl =
  match ty with
  | Term.Prod (a, b) ->
    let x, body = unbind b in
    let is_impl, rest =
      match impl with
      | i :: r -> (i, r)
      | []     -> (false, [])
    in
    let rest_params, ret = extract_params body rest in
    ((base_name x, a, is_impl) :: rest_params, ret)
  | _ -> ([], ty)

let rec extract_lambda_params tm impl =
  match tm with
  | Term.Abst (a, b) ->
    let x, body = unbind b in
    let is_impl, rest =
      match impl with
      | i :: r -> (i, r)
      | []     -> (false, [])
    in
    let rest_params, ret = extract_lambda_params body rest in
    ((base_name x, a, is_impl) :: rest_params, ret)
  | _ -> ([], tm)

let print_param ppf (name, ty, is_impl) =
  if is_impl then
    Format.fprintf ppf " [%s : %a]" name print_term ty
  else
    Format.fprintf ppf " (%s : %a)" name print_term ty

let print_symbol ppf sym =
  let name = sym.Term.sym_name in
  set_do_not_qualify true;
  set_print_domains true;
  Print.expo ppf sym.Term.sym_expo;
  Print.prop ppf sym.Term.sym_prop;
  Print.match_strat ppf sym.Term.sym_mstrat;
  Format.fprintf ppf "symbol %s" name;
  let sym_ty =
    Option.value
      (Hashtbl.find_opt symbol_types name)
      ~default:mk_Kind
  in
  let sym_def  = Hashtbl.find_opt symbol_defs name in
  let sym_impl = sym.Term.sym_impl in
  let is_proof_def = Hashtbl.mem symbol_asserts name in
  set_print_implicits true;
  (match sym_ty with
   | Term.Kind ->
     (* Definition with inferred type - extract params from lambda *)
     (match sym_def with
      | Some def when is_proof_def ->
        (* Pretty-print proof step: head on first line, args indented.
           Skip placeholder args (implicit parameters). *)
        set_print_implicits false;
        let rec collect_args = function
          | Term.Appl (f, a) ->
            let head, args = collect_args f in
            (head, args @ [a])
          | t -> (t, [])
        in
        let is_plac = function Term.Plac _ -> true | _ -> false in
        let head, args = collect_args def in
        let args = List.filter (fun a -> not (is_plac a)) args in
        Format.fprintf ppf " ≔@\n  @[<v>%a" print_term head;
        List.iter (fun a ->
          Format.fprintf ppf "@\n(%a)" print_term a
        ) args;
        Format.fprintf ppf "@]"
      | Some def ->
        let params, body = extract_lambda_params def sym_impl in
        if params <> [] then begin
          List.iter (print_param ppf) params;
          set_print_implicits false;
          Format.fprintf ppf " ≔ %a" print_term body
        end else begin
          set_print_implicits false;
          Format.fprintf ppf " ≔ %a" print_term def
        end
      | None -> ())
   | _ ->
     (* Has explicit type - extract params from Π-binders *)
     let params, ret_ty = extract_params sym_ty sym_impl in
     let n = List.length params in
     if params <> [] then
       List.iter (print_param ppf) params;
     set_print_implicits false;
     (match ret_ty with
      | Term.Kind -> ()
      | _ ->
        (* Print return type to a buffer so we can post-process *)
        let buf = Buffer.create 128 in
        let ppf_buf = Format.formatter_of_buffer buf in
        Format.fprintf ppf_buf "%a" print_term ret_ty;
        Format.pp_print_flush ppf_buf ();
        let ret_str = Buffer.contents buf in
        (* Apply @-prefix replacements for filled implicit args *)
        let ret_str = apply_explicit_replacements name ret_str in
        Format.fprintf ppf " : %s" ret_str);
     (* Print definition if present *)
     (match sym_def with
      | Some def ->
        Format.fprintf ppf " ≔ %a" print_term (unwrap_lambdas n def)
      | None -> ()));
  set_print_implicits false;
  set_print_domains false;
  set_do_not_qualify false;
  Format.fprintf ppf ";@.";
  (* If this symbol has an assertion type, emit assert ⊢ name : ty; *)
  (match Hashtbl.find_opt symbol_asserts name with
   | Some assert_ty ->
     set_do_not_qualify true;
     set_print_implicits false;
     Format.fprintf ppf "assert ⊢ %s : %a;@." name print_term assert_ty;
     set_do_not_qualify false
   | None -> ())

(* Print a single rule clause (LHS ↪ RHS) without keyword *)
let print_rule_clause ppf (sym, rule) =
  set_print_implicits true;
  set_do_not_qualify true;
  (* Check if this is a coercion rule (head symbol is "coerce") *)
  let is_coerce = sym.Term.sym_name = "coerce" in
  let is_eo_nil = sym.Term.sym_name = "{|eo::nil|}" in
  if is_coerce then
    Format.fprintf ppf "coerce"
  else
    (* Use @ prefix to force implicits on head symbol *)
    Format.fprintf ppf "@%s" sym.Term.sym_name;
  (* Print LHS args; implicits off for eo::nil so (+) not (@+ _) *)
  if is_eo_nil then set_print_implicits false;
  List.iter
    (fun arg -> Format.fprintf ppf " (%a)" print_term arg)
    rule.Term.lhs;

  (* Print RHS with implicits on: values solved during encoding (e.g. by
     fill_ite_implicits) are emitted explicitly instead of discarded, so
     the checker need not re-infer them; unsolved ones render as _. *)
  set_print_implicits true;
  Format.fprintf ppf " ↪ %a" print_term rule.Term.rhs;
  set_print_implicits false;
  set_do_not_qualify false

(* Print a group of rules for the same symbol, joined with "with" *)
let print_rules ppf rules =
  match rules with
  | [] -> ()
  | [(sym, _) as first] ->
    (* Single rule: use coerce_rule for coercion, rule otherwise *)
    let is_coerce = sym.Term.sym_name = "coerce" in
    if is_coerce then
      Format.fprintf ppf "coerce_rule %a;@." print_rule_clause first
    else
      Format.fprintf ppf "rule %a;@." print_rule_clause first
  | (sym, _) :: _ ->
    (* Check if coerce - coerce_rule doesn't support "with" *)
    let is_coerce = sym.Term.sym_name = "coerce" in
    if is_coerce then
      (* Print each coerce rule separately *)
      List.iter (fun r ->
        Format.fprintf ppf "coerce_rule %a;@." print_rule_clause r)
        rules
    else begin
      (* Multiple rules: join with "with" *)
      let first = List.hd rules in
      let rest = List.tl rules in
      let n_rest = List.length rest in
      Format.fprintf ppf "rule %a@." print_rule_clause first;
      List.iteri (fun i r ->
        if i = n_rest - 1 then
          Format.fprintf ppf "with %a;@." print_rule_clause r
        else
          Format.fprintf ppf "with %a@." print_rule_clause r)
        rest
    end

(* Each encoded command: symbol declarations + rules, printed in order *)
type output_item = {
  oi_syms  : sym list;
  oi_rules : (sym * rule) list;
}

let render_item item =
  let buf = Buffer.create 256 in
  let ppf = Format.formatter_of_buffer buf in
  List.iter (print_symbol ppf) item.oi_syms;
  print_rules ppf item.oi_rules;
  Format.pp_print_flush ppf ();
  strip_lp_escapes (String.trim (Buffer.contents buf))

let print_signature ppf ~prelude_module ~deps items =
  let open_deps =
    if deps = [] then [prelude_module] else deps
  in
  Format.fprintf ppf "require open %s;@.@."
    (String.concat " " open_deps);
  List.iter (fun item ->
    List.iter (print_symbol ppf) item.oi_syms;
    print_rules ppf item.oi_rules
  ) items

(* File operations *)
let rec mkdir_p dir =
  if not (Sys.file_exists dir) then begin
    mkdir_p (Filename.dirname dir);
    Sys.mkdir dir 0o755
  end

(* Build text replacements from alias table.
   E.g., "{|eo::String|}" → "Seq Char" *)
let alias_replacements () =
  let buf = Buffer.create 64 in
  let repls = ref [] in
  Hashtbl.iter (fun name target ->
    Buffer.clear buf;
    let ppf = Format.formatter_of_buffer buf in
    set_do_not_qualify true;
    Print.term ppf target;
    Format.pp_print_flush ppf ();
    set_do_not_qualify false;
    repls := (name, Buffer.contents buf) :: !repls
  ) alias_table;
  !repls

let write_lp_file filepath ~prelude_module ~deps items =
  let dir = Filename.dirname filepath in
  if dir <> "." && dir <> "" then mkdir_p dir;
  (* Separate alias rules (arity 0, head symbol is an alias) from other items *)
  let repls = alias_replacements () in
  let alias_names = List.map fst repls in
  let is_alias_rule (sym, rule) =
    rule.Term.arity = 0 && List.mem sym.Term.sym_name alias_names
  in
  let alias_items = ref [] in
  let other_items = List.map (fun item ->
    let aliases, others = List.partition is_alias_rule item.oi_rules in
    alias_items := aliases @ !alias_items;
    { item with oi_rules = others }
  ) items in
  (* Print main content to buffer for post-processing *)
  let buf = Buffer.create 4096 in
  let ppf = Format.formatter_of_buffer buf in
  print_signature ppf ~prelude_module ~deps other_items;
  Format.pp_print_flush ppf ();
  (* Post-process: replace alias names that Print.term inserts
     as implicit type arguments (not reachable by reduce_aliases).
     Use a single combined regex to avoid multiple full-string copies. *)
  let content = Buffer.contents buf in
  let content =
    if repls = [] then content
    else
      let pattern = String.concat "\\|"
        (List.map (fun (name, _) -> Str.quote name) repls) in
      let re = Str.regexp pattern in
      let repl_tbl = Hashtbl.create (List.length repls) in
      List.iter (fun (name, replacement) ->
        Hashtbl.replace repl_tbl name replacement) repls;
      Str.global_substitute re (fun s ->
        let matched = Str.matched_string s in
        match Hashtbl.find_opt repl_tbl matched with
        | Some r -> r
        | None -> matched
      ) content
  in
  (* Append alias rules (not post-processed) *)
  let alias_buf = Buffer.create 256 in
  let alias_ppf = Format.formatter_of_buffer alias_buf in
  if !alias_items <> [] then
    print_rules alias_ppf !alias_items;
  Format.pp_print_flush alias_ppf ();
  let oc = open_out filepath in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () ->
    output_string oc content;
    output_string oc (Buffer.contents alias_buf))

let generate_pkg_file output_dir pkg_name =
  let path = Filename.concat output_dir "lambdapi.pkg" in
  let oc = open_out path in
  Printf.fprintf oc "package_name = %s\n" pkg_name;
  Printf.fprintf oc "root_path = %s\n" pkg_name;
  close_out oc

let generate_prelude output_dir =
  let src = "src/Prelude.lp" in
  let dst = Filename.concat output_dir "Prelude.lp" in
  let ic  = open_in src in
  let oc  = open_out dst in
  (try
     while true do
       output_string oc (input_line ic ^ "\n")
     done
   with End_of_file -> ());
  close_in ic;
  close_out oc

(* LambdaPi checking *)
type check_result =
  | Check_ok
  | Check_error of string

let check_file ?(timeout=30) output_dir rel_path =
  let cmd =
    Printf.sprintf
      "cd %s && NO_COLOR=1 lambdapi check -c -w %s 2>&1"
      (Filename.quote output_dir) (Filename.quote rel_path)
  in
  (* Fork-based timeout: run the command in a child process so we can
     reliably kill the entire process tree via process-group kill. *)
  flush_all ();
  let pipe_r, pipe_w = Unix.pipe () in
  let pid = Unix.fork () in
  if pid = 0 then begin
    (* Child: become a new process group leader so the parent can
       kill us and all our descendants with a single signal. *)
    ignore (Unix.setsid ());
    Unix.close pipe_r;
    let ic = Unix.open_process_in cmd in
    let output_raw = In_channel.input_all ic in
    let status = Unix.close_process_in ic in
    let oc = Unix.out_channel_of_descr pipe_w in
    Marshal.to_channel oc (output_raw, status) [];
    close_out oc;
    exit 0
  end else begin
    (* Parent *)
    Unix.close pipe_w;
    let timed_out = ref false in
    let old_handler = Sys.signal Sys.sigalrm
      (Sys.Signal_handle (fun _ -> timed_out := true)) in
    let old_alarm = if timeout > 0 then Unix.alarm timeout else 0 in
    let rec wait () =
      try Unix.waitpid [] pid
      with Unix.Unix_error (Unix.EINTR, _, _) ->
        if !timed_out then begin
          (* Kill the entire process group *)
          (try Unix.kill (-pid) Sys.sigkill with Unix.Unix_error _ -> ());
          (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
          Unix.waitpid [] pid
        end else
          wait ()
    in
    let _, _ = wait () in
    ignore (Unix.alarm 0);
    Sys.set_signal Sys.sigalrm old_handler;
    if old_alarm > 0 then ignore (Unix.alarm old_alarm);
    if !timed_out then begin
      Unix.close pipe_r;
      Check_error "timeout"
    end else
    let ic = Unix.in_channel_of_descr pipe_r in
    let output_raw, status =
      try (Marshal.from_channel ic : string * Unix.process_status)
      with _ -> ("", Unix.WEXITED 1) in
    close_in ic;
  (* Get absolute path of output_dir for stripping *)
  let abs_output_dir =
    if Filename.is_relative output_dir then
      Filename.concat (Sys.getcwd ()) output_dir
    else output_dir
  in
  let output =
    output_raw
    |> String.trim
    (* Remove ANSI escape codes *)
    |> Str.global_replace (Str.regexp "\027\\[[0-9;]*m") ""
    (* Remove "Start checking ..." line *)
    |> Str.global_replace (Str.regexp "Start checking [^\n]*\n?") ""
    (* Strip output_dir prefix from paths, keeping relative path *)
    |> Str.global_replace (Str.regexp_string (abs_output_dir ^ "/")) ""
    (* Strip filename from location brackets, e.g. [foo/Bar.lp:27:5-102] -> [27:5-102] *)
    |> Str.global_replace (Str.regexp "\\[[^]]*\\.lp:\\([0-9][^]]*\\)\\]") "[\\1]"
    |> String.trim
  in
  (* Add newline after first location bracket: "[27:5-102] msg" -> "[27:5-102]\n  msg" *)
  let output =
    match Str.search_forward (Str.regexp "\\[[0-9][^]]*\\] ") output 0 with
    | n ->
      let matched = Str.matched_string output in
      let before = String.sub output 0 n in
      let bracket = String.sub matched 0 (String.length matched - 1) in (* drop trailing space *)
      let after = String.sub output (n + String.length matched) (String.length output - n - String.length matched) in
      before ^ bracket ^ "\n" ^ after
    | exception Not_found -> output
  in
  match status with
  | Unix.WEXITED 0   -> Check_ok
  | _                -> Check_error output
  end
