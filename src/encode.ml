(* encode.ml
   Eunoia to LambdaPi encoding *)

module EO = Syntax_eo
open Api_lp
open Lp_builders
open Resolve

(* Overload management *)
let overload_counts : (string, int) Hashtbl.t =
  Hashtbl.create 32

(* Name alias table: maps original escaped name to latest LP name
   when a symbol is redefined (e.g., across assume-push/step-pop scopes) *)
let name_aliases : (string, string) Hashtbl.t =
  Hashtbl.create 32

let reset_overloads () =
  Hashtbl.clear overload_counts;
  Hashtbl.clear name_aliases;
  reset_symbol_storage ()

(* Resolve a name through the alias table *)
let resolve_name name =
  match Hashtbl.find_opt name_aliases name with
  | Some alias -> alias
  | None -> name

(* Get a unique name for potentially overloaded symbols *)
let unique_name name =
  let escaped = esc name in
  match Hashtbl.find_opt overload_counts escaped with
  | None ->
    Hashtbl.add overload_counts escaped 1;
    escaped
  | Some n ->
    Hashtbl.replace overload_counts escaped (n + 1);
    (* Insert suffix inside {|...|} delimiters if present *)
    let new_name =
      if String.length escaped > 4
         && String.sub escaped 0 2 = "{|"
         && String.sub escaped (String.length escaped - 2) 2 = "|}"
      then
        let inner = String.sub escaped 2 (String.length escaped - 4) in
        Printf.sprintf "{|%s_%d|}" inner n
      else
        esc (Printf.sprintf "%s_%d" escaped n)
    in
    (* Record alias so references to the original resolve to the latest *)
    Hashtbl.replace name_aliases escaped new_name;
    new_name

(* Assumption stack for assume-push / step-pop scope handling *)
let assumption_stack : EO.term list ref = ref []
let push_assumption t = assumption_stack := t :: !assumption_stack
let pop_assumption () = match !assumption_stack with
  | t :: rest -> assumption_stack := rest; t
  | [] -> failwith "pop_assumption: empty stack"
let reset_assumptions () = assumption_stack := []
let assumption_stack_depth () = List.length !assumption_stack

(* ============================================================
   Elaboration interface — delegates to Elaborate module
   ============================================================ *)

module Elab = Elaborate

let set_signature = Elab.set_signature
let snapshot_base_sig = Elab.snapshot_base_sig
let set_signature_overlay = Elab.set_signature_overlay

(* ============================================================
   Literal encoding
   ============================================================ *)

let enc_string_literal s =
  let quoted = "\"" ^ s ^ "\"" in
  let sym =
    try Core.Sign.find Core.Sign.Ghost.sign quoted
    with Not_found ->
      let string_ty = mk_Symb (find "String") in
      Core.Sign.add_symbol Core.Sign.Ghost.sign
        Core.Term.Public Core.Term.Const Core.Term.Eager true
        (Pos.none quoted) None string_ty []
  in
  mk_Symb sym

let enc_literal = function
  | Literal.Numeral n ->
    add_args (mk_Symb (find "of_Z")) [Enc_numerals.enc_int n]
  | Literal.Rational (n, d) ->
    add_args (mk_Symb (find "of_Q")) [Enc_numerals.enc_rational n d]
  | Literal.String s -> enc_string_literal s
  | lit -> failf "enc_literal: unsupported literal %s" (Literal.literal_str lit)

(* ============================================================
   Binder helpers — for proof-level forall/exists encoding
   ============================================================ *)

(* Check if a symbol has the :binder attribute in the EO signature *)
let is_binder_sym s =
  Elab.find_all_eo_symbols s |> List.exists (fun (_s', k) ->
    match k with
    | EO.Decl (_, _, Some (EO.Binder _)) -> true
    | _ -> false)

(* Extract (name, type) pairs from an elaborated variable list.
   The list is: eo::List::cons (eo::var name ty) (eo::List::cons ... eo::List::nil)
   Variables may also appear without the list wrapper (single var). *)
let rec extract_eo_var_list = function
  | EO.Apply (op, [EO.Apply (var_op, [EO.Literal (Literal.String name); ty]); rest])
    when op = EO.Builtin.eo_list_cons && var_op = EO.Builtin.eo_var ->
    (name, ty) :: extract_eo_var_list rest
  | EO.Apply (op, [EO.Apply (var_op, [EO.Symbol name; ty]); rest])
    when op = EO.Builtin.eo_list_cons && var_op = EO.Builtin.eo_var ->
    (name, ty) :: extract_eo_var_list rest
  | EO.Symbol s when s = EO.Builtin.eo_list_nil -> []
  (* Single var without list wrapper *)
  | EO.Apply (var_op, [EO.Literal (Literal.String name); ty])
    when var_op = EO.Builtin.eo_var ->
    [(name, ty)]
  | EO.Apply (var_op, [EO.Symbol name; ty])
    when var_op = EO.Builtin.eo_var ->
    [(name, ty)]
  | _ -> []  (* Can't extract — fall back to no binding *)

(* ============================================================
   Term encoding — consumes elaborated EO terms
   ============================================================ *)

(* Encode an elaborated EO term (output of Elab.elab) into LambdaPi.
   Elaborated terms are already normalized: no define expansion, no n-ary
   folding needed. This is a pure structural translation. *)
let rec enc_elaborated ctx : EO.term -> term = function
  | EO.Symbol s when s = EO.Builtin.ty_type -> eo_type ()
  | EO.Symbol s ->
    (match ctxt_find ctx (esc s) with
     | Some v -> mk_Vari v
     | None -> enc_sym (get_sym (resolve_name (esc s))))
  | EO.Literal lit -> enc_literal lit
  | EO.Apply (s, [ty; tm]) when s = EO.Builtin.eo_as || s = EO.Builtin.ty_as ->
    eo_as (enc_elaborated ctx ty) (enc_elaborated ctx tm)
  | EO.Apply (s, [f; x]) when s = EO.Builtin.ty_app ->
    hol_app (enc_elaborated ctx f) (enc_elaborated ctx x)
  | EO.Apply (s, args) when s = EO.Builtin.ty_arrow ->
    enc_arrow_eo ctx args
  (* eo::nil f ty — eagerly evaluate by looking up f's nil terminator
     and substituting type parameters with ty. This avoids emitting
     {|eo::nil|} calls whose implicit args LP cannot infer. *)
  | EO.Apply (op, [EO.Symbol f; ty_arg]) when op = EO.Builtin.eo_nil ->
    let nil_term_opt = match Elab.lookup_eo_symbol f with
      | Some (EO.Decl (ps, _, Some attr)) ->
        let nil_t = match attr with
          | EO.RightAssocNil t | EO.LeftAssocNil t
          | EO.RightAssocNilNSN t | EO.LeftAssocNilNSN t -> Some t
          | _ -> None
        in
        (match nil_t with
         | Some t ->
           (* Substitute type params (those with type Type) with ty_arg *)
           let type_params = List.filter_map (fun (n, ty, _) ->
             if ty = EO.Symbol EO.Builtin.ty_type then Some n else None) ps in
           let rec subst = function
             | EO.Symbol s when List.mem s type_params -> ty_arg
             | EO.Apply (s, args) -> EO.Apply (s, List.map subst args)
             | EO.Bind (s, vs, body) -> EO.Bind (s, vs, subst body)
             | t -> t
           in
           Some (subst t)
         | None -> None)
      | _ -> None
    in
    (match nil_term_opt with
     | Some t -> enc_elaborated ctx t
     | None ->
       let head = enc_sym (get_sym (resolve_name (esc op))) in
       add_args head (List.map (enc_elaborated ctx) [EO.Symbol f; ty_arg]))
  (* eo::var reference — look up the variable in context if bound *)
  | EO.Apply (op, [_ty; EO.Literal (Literal.String name)])
    when op = EO.Builtin.eo_var ->
    let s_esc = esc name in
    (match ctxt_find ctx s_esc with
     | Some v -> mk_Vari v
     | None ->
       (* Not in context — encode as eo::var application (e.g., in var lists) *)
       let head = enc_sym (get_sym (esc EO.Builtin.eo_var)) in
       add_args head [enc_elaborated ctx _ty;
                      enc_elaborated ctx (EO.Literal (Literal.String name))])
  | EO.Apply (op, [_ty; EO.Symbol name])
    when op = EO.Builtin.eo_var ->
    let s_esc = esc name in
    (match ctxt_find ctx s_esc with
     | Some v -> mk_Vari v
     | None ->
       let head = enc_sym (get_sym (esc EO.Builtin.eo_var)) in
       add_args head [enc_elaborated ctx _ty;
                      enc_elaborated ctx (EO.Symbol name)])
  (* Binder application (exists, forall): extract vars, bind in lambda *)
  | EO.Apply (s, [list_arg; body]) when is_binder_sym s ->
    let vars = extract_eo_var_list list_arg in
    let head = enc_sym (get_sym (resolve_name (esc s))) in
    (* Encode the list arg (passed to the binder symbol) *)
    let list_enc = enc_elaborated ctx list_arg in
    (* Build a lambda over the body, binding each variable *)
    let body_enc = enc_binder_body ctx vars body in
    add_args head [list_enc; body_enc]
  | EO.Apply (s, ts) ->
    let head = enc_sym (get_sym (resolve_name (esc s))) in
    add_args head (List.map (enc_elaborated ctx) ts)
  | EO.Bind (op, xs, body) when op = EO.Builtin.eo_define ->
    enc_let_eo ctx xs body
  | EO.Bind (s, _, _) ->
    failf "enc_elaborated: unexpected Bind(%s)" s

(* Encode an elaborated arrow type *)
and enc_arrow_eo ctx = function
  | [] -> fail "Empty arrow type"
  | [t] -> enc_elaborated ctx t
  | EO.Apply (op, [ty; EO.Symbol s]) :: rest when op = EO.Builtin.eo_var ->
    let s_esc = esc s in
    let eo_ty = enc_elaborated ctx ty in
    let type_of_s = tau_of eo_ty in
    let v = new_var s_esc in
    let ctx' = ctxt_add ctx v type_of_s in
    let body = enc_arrow_eo ctx' rest in
    let lam = mk_Abst (type_of_s, bind_var v body) in
    hol_dep_arrow eo_ty lam
  | EO.Apply (op, [EO.Symbol s]) :: rest when op = EO.Builtin.eo_quote ->
    let s_esc = esc s in
    let type_of_s =
      match List.find_opt (fun (v, _, _) -> base_name v = s_esc) ctx with
      | Some (_, ty, _) -> ty
      | None ->
        let ctx_vars = List.map (fun (v, _, _) -> base_name v) ctx in
        failf "enc_arrow_eo: variable `%s` not in context. Available: [%s]"
          s (String.concat ", " ctx_vars)
    in
    let eo_type_of_s = un_tau type_of_s in
    let v = new_var s_esc in
    let ctx' = ctxt_add ctx v type_of_s in
    let body = enc_arrow_eo ctx' rest in
    let lam = mk_Abst (type_of_s, bind_var v body) in
    hol_dep_arrow eo_type_of_s lam
  | t :: rest ->
    hol_arrow (enc_elaborated ctx t) (enc_arrow_eo ctx rest)

(* Encode an elaborated let-binding *)
and enc_let_eo ctx xs body =
  match xs with
  | [] -> enc_elaborated ctx body
  | (name, rhs) :: rest ->
    let rhs_enc = enc_elaborated ctx rhs in
    let ty = mk_Plac false in
    let v = new_var (esc name) in
    let ctx' = ctxt_add ctx v ty in
    let body_enc = enc_let_eo ctx' rest body in
    Core.Term.mk_LLet (ty, rhs_enc, bind_var v body_enc)

(* Encode the body of a binder (forall/exists) as a lambda, binding
   each variable from the extracted list into the context. *)
and enc_binder_body ctx vars body =
  match vars with
  | [] -> enc_elaborated ctx body
  | (name, ty_eo) :: rest ->
    let s_esc = esc name in
    let eo_ty = enc_elaborated ctx ty_eo in
    let type_of_v = tau_of eo_ty in
    let v = new_var s_esc in
    let ctx' = ctxt_add ctx v type_of_v in
    let inner = enc_binder_body ctx' rest body in
    mk_Abst (type_of_v, bind_var v inner)

and enc_term ps ctx t =
  enc_elaborated ctx (Elab.elab ps t)

(* Parameter encoding *)
let enc_params ps =
  let ctx, impl =
    List.fold_left
      (fun (ctx, acc) (str, ty, atts) ->
         let v = new_var (esc str) in
         (* Type parameters (T : Type) have type Set (= τ {|eo::Type|}) *)
         let ty' = tau_of (enc_term [] ctx ty) in
         let ctx' = ctxt_add ctx v ty' in
         let is_impl = List.mem EO.Implicit atts in
         (ctx', is_impl :: acc))
      (empty_ctxt, [])
      ps
  in
  (* Context is built in reverse order (ctxt_add prepends), which is what
     ctxt_to_prod/ctxt_to_abst expect (they use fold_left, wrapping first
     element as innermost binder, producing Π p_n. ... Π p_1. body).

     impl is accumulated in reverse order [p_n_impl; ...; p_1_impl], but
     the final type has params in original order (p_1 outermost), so we
     must reverse impl to match: [p_1_impl; ...; p_n_impl]. *)
  (ctx, List.rev impl)

(* Constant encoding *)
type enc_result = {
  syms  : sym list;
  rules : (sym * rule) list;
}

let empty_result = { syms = []; rules = [] }

(* Convert variables in a term to pattern variables.
   Takes a context (from enc_params) and replaces occurrences of ctx vars
   with pattern vars ($0 = innermost/most-recent binder). *)
let bind_pvars ctx term =
  let idx_of : (string, int) Hashtbl.t = Hashtbl.create (List.length ctx) in
  List.iteri (fun i (v, _, _) -> Hashtbl.replace idx_of (base_name v) i) ctx;
  (* Avoid capturing/shadowing: if we descend under a binder, variables with the
     binder's name must not become pattern variables. *)
  let rec go bound = function
    | Core.Term.Vari v as t ->
      let name = base_name v in
      if List.mem name bound then t
      else
        (match Hashtbl.find_opt idx_of name with
         | Some idx -> mk_Patt (Some idx, name, [||])
         | None -> t)
    | Core.Term.Symb s as t ->
      let name = s.Core.Term.sym_name in
      if List.mem name bound then t
      else
        (match Hashtbl.find_opt idx_of name with
         | Some idx -> mk_Patt (Some idx, name, [||])
         | None -> t)
    | Core.Term.Meta (m, ts) ->
      (match Timed.(!(m.Core.Term.meta_value)) with
       | None -> mk_Plac false
       | Some mb -> go bound (Core.Term.msubst mb ts))
    | Core.Term.Appl (t1, t2) ->
      mk_Appl (go bound t1, go bound t2)
    | Core.Term.Abst (ty, b) ->
      let v, body = unbind b in
      mk_Abst (go bound ty, bind_var v (go (base_name v :: bound) body))
    | Core.Term.Prod (ty, b) ->
      let v, body = unbind b in
      mk_Prod (go bound ty, bind_var v (go (base_name v :: bound) body))
    | Core.Term.LLet (ty, t, b) ->
      let v, body = unbind b in
      Core.Term.mk_LLet
        (go bound ty, go bound t, bind_var v (go (base_name v :: bound) body))
    | t -> t
  in
  go [] term

let enc_decl str ps ty attr =
  let ctx, impl = enc_params ps in
  let body_ty = tau_of (enc_term [] ctx ty) in
  let body_ty = resolve_term ~ctx body_ty in
  let ty', _ = ctxt_to_prod ctx body_ty in
  let sym = add_constant ~impl (unique_name str) ty' in
  (* Generate eo::nil rule for operators with nil terminators.
     E.g., (declare-const and (-> Bool Bool Bool) :right-assoc-nil true)
     generates: rule {|eo::nil|} and Bool ↪ true; *)
  let nil_term_opt = match attr with
    | Some (EO.RightAssocNil t)    -> Some t
    | Some (EO.LeftAssocNil t)     -> Some t
    | Some (EO.RightAssocNilNSN t) -> Some t
    | Some (EO.LeftAssocNilNSN t)  -> Some t
    | _ -> None
  in
  let nil_rules = match nil_term_opt with
    | None -> []
    | Some nil_eo_term ->
      (* Extract return type from arrow: (-> T1 ... Tn) → Tn *)
      let ret_type_eo = match ty with
        | EO.Apply ("->", (_ :: _ as ts)) ->
          List.rev ts |> List.hd
        | _ -> ty
      in
      let eo_nil_sym = get_sym (esc "eo::nil") in
      (* Check if the nil term references type parameters (e.g. ($zero T)).
         If so, encode with params in context and use pattern variables. *)
      let nil_refs_param = List.exists (fun (n, _, _) ->
        EO.term_contains_symbol n nil_eo_term) ps in
      if nil_refs_param then begin
        (* Polymorphic nil: encode with type params in context.
           E.g. + [T] with nil ($zero T) generates:
             rule eo::nil _ _ (+) ($T) ↪ $zero $T
           The operator carries placeholder implicit args for correctness;
           print_implicits is off for LHS args so they don't show. *)
        let nil_enc = enc_term ps ctx nil_eo_term in
        let ret_type_enc = enc_term ps ctx ret_type_eo in
        let op_enc =
          let n_impl = List.length (List.filter Fun.id impl) in
          if n_impl > 0 then
            let args = List.init n_impl (fun _ -> mk_Plac false) in
            add_args (mk_Symb sym) args
          else mk_Symb sym
        in
        let nil_rhs = bind_pvars ctx nil_enc in
        let ret_lhs = bind_pvars ctx ret_type_enc in
        let rule = mk_rule_record ctx
          [mk_Plac false; mk_Plac false; op_enc; ret_lhs] nil_rhs in
        [(eo_nil_sym, rule)]
      end else begin
        (* Concrete nil: infer return type from nil literal.
           E.g. and with nil true generates:
             rule eo::nil _ _ and Bool ↪ true *)
        let nil_enc = enc_term [] empty_ctxt nil_eo_term in
        let ret_type_enc =
          let is_param = List.exists (fun (n, _, _) -> n = (match ret_type_eo with EO.Symbol s -> s | _ -> "")) ps in
          if is_param then
            match infer_type empty_ctxt nil_enc with
            | Some ty -> un_tau ty
            | None -> enc_term [] empty_ctxt ret_type_eo
          else
            enc_term [] empty_ctxt ret_type_eo
        in
        let op_enc =
          let n_impl = List.length (List.filter Fun.id impl) in
          if n_impl > 0 then
            let args = List.init n_impl (fun _ -> ret_type_enc) in
            add_args (mk_Symb sym) args
          else mk_Symb sym
        in
        let rule = mk_rule_record []
          [mk_Plac false; mk_Plac false; op_enc; ret_type_enc] nil_enc in
        [(eo_nil_sym, rule)]
      end
  in
  { syms = [sym]; rules = nil_rules; }

(* Check if an Eunoia AST term contains eo::requires *)
let rec has_eo_requires = function
  | EO.Apply (s, _) when s = EO.Builtin.eo_requires -> true
  | EO.Apply (_, args) -> List.exists has_eo_requires args
  | EO.Bind (_, _, body) -> has_eo_requires body
  | _ -> false

let enc_defn str ps tm ty_opt =
  match ps with
  | [] ->
    (match tm with
     | EO.Symbol _ ->
       (* Symbol alias — inlined by the elaborator, skip *)
       empty_result
     | _ ->
       (* Nullary define with compound body: emit as an LP definition *)
       let ctx = empty_ctxt in
       let body = enc_term [] ctx tm in
       let ty = Option.map (fun ty -> tau_of (enc_term [] ctx ty)) ty_opt in
       let sym = add_definition (unique_name str) ty body in
       { syms = [sym]; rules = []; })
  | _ ->
    let ctx, impl = enc_params ps in
    let body_raw = enc_term ps ctx tm in
    let expected_ty = Option.map (fun ty -> tau_of (enc_term ps ctx ty)) ty_opt in
    let body = resolve_term ~ctx ?expected_ty body_raw in
    (* When the body contains eo::requires (which constrains type params,
       causing the inferred body type to differ from the parametric type),
       encode as a sequential symbol + rule instead of a definition.
       This preserves the parametric return type (e.g., τ T instead of
       τ (?? ... Int Real)), which is needed for downstream type checking. *)
    let has_type_param =
      List.exists (fun (_, ty, _) -> ty = EO.Symbol EO.Builtin.ty_type) ps
    in
    if has_eo_requires tm && has_type_param then begin
      (* For defines with eo::requires and type params, encode as a
         sequential symbol + rule to preserve the parametric return type
         (LP's inference would over-specialize due to eo::requires).
         Infer return type: use last param's type if concrete, else first
         Type parameter. *)
      let return_ty_enc =
        (* Check if the last parameter has a concrete (non-type-variable) type *)
        let last_param_ty = match List.rev ps with
          | (_, ty, _) :: _ ->
            let is_type_param name =
              List.exists (fun (n, t, _) -> n = name && t = EO.Symbol EO.Builtin.ty_type) ps
            in
            (match ty with
             | EO.Symbol s when is_type_param s -> None  (* type variable *)
             | _ -> Some ty)  (* concrete type like Bool, Int, etc. *)
          | [] -> None
        in
        match last_param_ty with
        | Some ret_ty -> tau_of (enc_term ps ctx ret_ty)
        | None ->
          (* Fallback: use first Type parameter *)
          let type_param_name =
            List.find_map (fun (name, ty, _) ->
              if ty = EO.Symbol EO.Builtin.ty_type then Some (esc name) else None) ps
          in
          match type_param_name with
          | Some name ->
            (match List.find_map (fun (v, _, _) ->
                     if Core.Term.base_name v = name then Some v else None)
                     (List.rev ctx) with
             | Some tv -> tau_of (mk_Vari tv)
             | None -> tau_of (mk_Plac false))
          | None -> tau_of (mk_Plac false)
      in
      begin match return_ty_enc with
      | body_ty ->
        let body_ty = resolve_term ~ctx body_ty in
        let ty, _ = Core.Ctxt.to_prod ctx body_ty in
        let sym = add_sequential ~impl (unique_name str) ty in
        (* Build rule: sym $x1 ... $xn ↪ body *)
        let lhs_args =
          let n = List.length ctx in
          List.mapi (fun i (v, _, _) ->
            mk_Patt (Some (n - 1 - i), base_name v, [||])) (List.rev ctx)
        in
        let rhs = bind_pvars ctx body in
        let rule = mk_rule_record ctx lhs_args rhs in
        { syms = [sym]; rules = [(sym, rule)]; }
      end
    end else begin
      let tm' = ctxt_to_abst ctx body in
      { syms = [add_definition ~impl (unique_name str) None tm'];
        rules = []; }
    end

(* Rule encoding for programs *)

(* Encode a program case as a rewrite rule *)
let enc_case eo_ps ctx impl_ctx sym ?(wildcard_impl_vars=false) ?expected_ty (t1, t2 : EO.term * EO.term) =

  let l_res = enc_term eo_ps ctx t1 |> resolve_term ~debug:!verbose ~ctx in
  let r_res = enc_term eo_ps ctx t2 |> resolve_term ~debug:!verbose ~ctx in

  let enc_rhs encoded =
    let coerced = match expected_ty with
      | Some exp_ty -> coerce_int_to_lit ctx encoded exp_ty
      | None -> encoded
    in
    coerced |> bind_pvars ctx
  in

  (* For the LHS, resolution infers the implicit args from the explicit
     pattern args. We keep the resolved implicit args when they are fully
     resolved (e.g., Seq $U instead of bare $T when the pattern refines
     the type). When resolution leaves unsolved metas, we fall back to the
     impl_ctx variable to ensure pattern variables are bound in the LHS. *)
  let enc_lhs resolved =
    let resolved = strip_eo_as resolved in
    let head, args = Core.Term.get_args resolved in
    let is_our_sym = match head with
      | Core.Term.Symb s -> s == sym
      | _ -> false
    in
    if is_our_sym then begin
      let n_impl = List.length impl_ctx in
      let resolved_impl = if n_impl <= List.length args
        then List.filteri (fun i _ -> i < n_impl) args
        else []
      in
      let explicit_args = if n_impl <= List.length args
        then List.filteri (fun i _ -> i >= n_impl) args
        else args
      in
      (* For each implicit arg: use the resolved version if it has no
         unsolved metas, otherwise fall back to the impl_ctx variable. *)
      let impl_vars = List.rev_map (fun (v, _, _) -> mk_Vari v) impl_ctx in
      let is_impl_var t =
        if not wildcard_impl_vars then false
        else
          (* Unfold solved metas to check the underlying value *)
          let t' = match t with
            | Core.Term.Meta (m, ts) ->
              (match Timed.(!(m.Core.Term.meta_value)) with
               | Some mb -> Core.Term.msubst mb ts
               | None -> t)
            | _ -> t
          in
          match t' with
          | Core.Term.Vari v ->
            List.exists (fun (iv, _, _) ->
              Core.Term.eq_vars v iv) impl_ctx
          | _ -> false
      in
      let impl_args = List.map2 (fun resolved_arg fallback ->
        if is_impl_var resolved_arg then mk_Plac false
        else if has_unsolved_metas resolved_arg then fallback
        else resolved_arg
      ) resolved_impl impl_vars in
      (* Apply nonvar_metas_to_plac selectively: only to args that
         contain Stdlib.Z's int or unsolved metas. *)
      let cleanup_if_needed t =
        if has_unsolved_metas t || has_stdlib_int t
        then nonvar_metas_to_plac t
        else t
      in
      let final_impl = List.map cleanup_if_needed impl_args in
      let final_explicit = List.map cleanup_if_needed explicit_args in
      let new_args = final_impl @ final_explicit in
      bind_pvars ctx (add_args (mk_Symb sym) new_args)
    end else
      bind_pvars ctx resolved
  in

  let l, rhs = enc_lhs l_res, enc_rhs r_res in
  let _,lhs = Core.Term.get_args l in
  (* LHS and RHS are resolved independently, so an implicit may resolve to a
     context variable on the RHS while its LHS occurrence degraded to a
     wildcard — lambdapi rejects such rules ("Variable must be in LHS").
     Demote RHS pattern variables unbound in the LHS to wildcards; the SR
     checker re-solves them from the LHS typing. *)
  let lhs_pvar_names =
    let names = ref SSet.empty in
    List.iter (fun t ->
      ignore (term_map (fun t ->
        (match t with
         | Core.Term.Patt (_, n, _) -> names := SSet.add n !names
         | _ -> ());
        None) t)) lhs;
    !names
  in
  let rhs = term_map (function
    | Core.Term.Patt (_, n, _) when not (SSet.mem n lhs_pvar_names) ->
      Some (mk_Plac false)
    | _ -> None) rhs
  in
  (sym, mk_rule_record ctx lhs rhs)

let enc_prog str ps doms ran cases =
  let ctx, _ = enc_params ps in
  let ty_raw = EO.Apply (EO.Builtin.ty_arrow, doms @ [ran]) in
  let body_ty_raw = tau_of (enc_term ps ctx ty_raw) in
  let body_ty = resolve_term ~ctx body_ty_raw in
  (* Variables from ctx that are free in the type become implicit params *)
  let ty, impl, impl_ctx = impl_from_free_vars ctx body_ty in
  (* If the symbol already exists (forward declaration), reuse it
     and only encode the rules — no new symbol declaration. *)
  let escaped = esc str in
  let existing = Api_lp.find_symbol escaped in
  let sym = match existing with
    | Some s -> s
    | None   -> add_sequential ~impl (unique_name str) ty
  in
  (* Detect programs with both Int and Real param types: these need
     wildcard implicits to avoid type preservation failures with
     non-reducible type union functions like $arith_typeunion *)
  let wildcard_impl_vars =
    let param_types = List.map (fun (_, ty, _) -> ty) ps in
    let has t = List.exists (fun ty -> ty = t) param_types in
    has (EO.Symbol "Int") && has (EO.Symbol "Real")  (* CPC-specific names, not builtins *)
  in
  (* Compute expected type for RHS: τ(range) *)
  let rhs_expected_ty = tau_of (enc_term ps ctx ran) in
  let rules =
    List.map (fun (lhs, rhs) ->
      enc_case ps ctx impl_ctx sym ~wildcard_impl_vars ~expected_ty:rhs_expected_ty (lhs, rhs))
    cases
  in
  (* Forward-declared symbol: return no syms so the declaration is
     not printed again.  The rules appear at this position in the
     output since each enc_result is printed in order. *)
  match existing with
  | Some _ -> { syms = []; rules; }
  | None   -> { syms = [sym]; rules; }

let enc_ltrl cat ty =
  let result = Enc_numerals.enc_ltrl ~enc_term_fn:enc_term cat ty in
  { syms = result.Enc_numerals.syms; rules = result.Enc_numerals.rules }

(* Rule encoding for declare-rule *)

(* Get the Proof symbol from prelude *)
let proof_sym () = find "Proof"

(* Build Proof(t) application *)
let mk_proof t = mk_Appl (mk_Symb (proof_sym ()), t)

(* Encode a declare-rule.

   For rules with :args, we generate:

     symbol <name>_aux [<type_params>] : τ T1 → ... → τ Tn → TYPE;
     rule <name>_aux <pattern1> ... <patternN>
       ↪ Proof <prem1> → ... → Proof <premM> → Proof <conclusion>;

     symbol <name> [<type_params>] :
       Π x1 : τ T1, ... Π xn : τ Tn, <name>_aux x1 ... xn;

   For rules without :args (only :premises), we generate:

     symbol <name> [<type_params>] (p1 : τ T1) ... :
       Proof <prem1> → ... → Proof <premM> → Proof <conclusion>;
*)
let enc_rule str ps (rdec : EO.rule_dec) =
  (* :assumption F — the assumption variable should be explicit in the LP type,
     since LP can't infer it. We add it to the args so it's treated as explicit. *)
  let assm_names = match rdec.assm with
    | Some (EO.Symbol s) -> [esc s]
    | _ -> []
  in
  (* Ignore reqs for now - should wrap conclusion in eo::requires *)
  let _ = rdec.reqs in

  (* For :premise-list rules, add the premise-list pattern as an arg
     so it goes through the _aux pattern-matching path. The premise
     becomes Proof E where E is the folded formula. *)
  let args, prems, is_premise_list, n_explicit_args = match rdec.prem with
    | None -> (rdec.args, [], false, List.length rdec.args)
    | Some (EO.Simple ts) ->
      (* Only add premise formulas to _aux args when the rule already has
         non-trivial :args (patterns).  Rules with simple/no :args use the
         simple path where premises become Proof arrows directly. *)
      let has_nontrivial_args = not (List.for_all (function
        | EO.Symbol s -> EO.prm_mem s ps
        | _ -> false) rdec.args) && rdec.args <> [] in
      if has_nontrivial_args then
        (ts @ rdec.args, ts, false, List.length rdec.args)
      else
        (rdec.args, ts, false, List.length rdec.args)
    | Some (EO.PremiseList (pattern, _op)) ->
      (* Add the pattern as the first arg — enc_step passes formula_args
         (the folded premise formula) before :args, so the LP type must
         bind the premise-list variable first to match. *)
      ([pattern] @ rdec.args, [pattern], true, List.length rdec.args)
  in

  let conc = match rdec.conc with
    | EO.Conclusion t | EO.ConclusionExplicit t -> t
  in

  let ctx, _ = enc_params ps in

  (* Helper: build Proof p1 → Proof p2 → ... → Proof conclusion *)
  let build_proof_arrow prems conc_term =
    let conc_proof = mk_proof conc_term in
    List.fold_right
      (fun prem acc ->
         let prem_proof = mk_proof prem in
         mk_Prod (prem_proof, bind_var (new_var "_") acc))
      prems conc_proof
  in

  (* Check if an arg is a simple variable reference (not a pattern) *)
  let is_simple_arg = function
    | EO.Symbol s -> EO.prm_mem s ps  (* It's a parameter reference *)
    | _ -> false
  in

  (* Check if ALL args are simple variable references *)
  let all_args_simple = List.for_all is_simple_arg args in

  (* Premises and conclusions are formulas of type τ Bool.
     Passing this as expected_ty helps LambdaPi resolve polymorphic return types. *)
  let tau_bool = tau_of (mk_Symb (find "Bool")) in

  if args = [] || all_args_simple then begin
    (* No :args - simple rule with just premises and conclusion *)
    (* Encode premises and conclusion *)
    let prems_enc = List.map (fun p -> enc_term ps ctx p |> resolve_term ~debug:!verbose ~ctx ~expected_ty:tau_bool) prems in
    let conc_enc = enc_term ps ctx conc |> resolve_term ~debug:!verbose ~ctx ~expected_ty:tau_bool in

    (* If the conclusion has unsolved metas AND contains eo::ite (whose
       return type depends on an irreducible condition, preventing LambdaPi
       from re-inferring the types), replace unsolved metas with the first
       Set-typed variable from the context, and emit the symbol declaration
       as raw text with print_implicits=true to make the filled args visible. *)
    let rec has_eo_ite = function
      | Core.Term.Symb s -> s.Core.Term.sym_name = "{|eo::ite|}"
      | Core.Term.Appl (t1, t2) -> has_eo_ite t1 || has_eo_ite t2
      | _ -> false
    in
    let needs_explicit = has_unsolved_metas conc_enc && has_eo_ite conc_enc in
    let conc_enc, replacements =
      if needs_explicit then
        let type_vars = List.filter_map (fun (v, ty, _) ->
          match ty with
          | Core.Term.Appl (Core.Term.Symb s1, Core.Term.Symb s2)
            when s1.Core.Term.sym_name = "τ"
              && s2.Core.Term.sym_name = "{|eo::Type|}" -> Some v
          | _ -> None) ctx in
        match type_vars with
        | tv :: _ ->
          let solved = solve_set_metas_to conc_enc (mk_Vari tv) in
          (* Collect relation symbols that had unsolved metas filled *)
          let tv_name = Core.Term.base_name tv in
          let repls = ref [] in
          let rec find_relations = function
            | Core.Term.Appl _ as t ->
              let head, args = Core.Term.get_args t in
              (match head with
               | Core.Term.Symb s when
                 (let n = s.Core.Term.sym_name in
                  n = ">" || n = "<" || n = ">=" || n = "<=" || n = "=") &&
                 s.Core.Term.sym_impl <> [] ->
                 let n_impl = List.length s.Core.Term.sym_impl in
                 let impl_args = List.filteri (fun i _ -> i < n_impl) args in
                 let all_same_var = List.for_all (fun a ->
                   match a with
                   | Core.Term.Vari v -> Core.Term.base_name v = tv_name
                   | _ -> false) impl_args in
                 if all_same_var then
                   let impl_str = String.concat " " (List.map (fun _ -> tv_name) impl_args) in
                   repls := (s.Core.Term.sym_name, impl_str) :: !repls
               | _ -> ());
              List.iter find_relations args
            | _ -> ()
          in
          find_relations solved;
          (solved, !repls)
        | [] -> (conc_enc, [])
      else (conc_enc, [])
    in

    (* Build the body type in layers:
       1. Core: Proof conclusion
       2. Premises: Proof prem1 → ... → Proof premN → core
       3. Explicit args (:args, :assumption): bind as (x : τ T) → ...
       4. Implicit params: whatever is still free, bound as [x : τ T] → ... *)
    let core_ty = build_proof_arrow prems_enc conc_enc in

    (* Determine which params are explicit args *)
    let args_names = List.filter_map (function
      | EO.Symbol s -> Some (esc s)
      | _ -> None) args in
    let args_names = args_names @ assm_names in

    (* Bind explicit arg params around the core type.
       Order must match enc_step's application order, which is:
         formula_args @ args_enc @ prems_enc
       i.e. premise-list formula first (if any), then :args in order,
       then the proof.  to_prod wraps the first element as innermost
       binder, so we pass the *reverse* of the desired LP param order. *)
    let explicit_ctx =
      let ctx_by_name = List.map (fun ((v, _, _) as entry) ->
        (base_name v, entry)) ctx in
      let ordered = List.filter_map (fun name ->
        List.assoc_opt name ctx_by_name) args_names in
      List.rev ordered
    in
    let after_explicit, _ = Core.Ctxt.to_prod explicit_ctx core_ty in

    (* Find remaining free vars — these become implicit *)
    let ty, impl, _implicit_ctx = impl_from_free_vars ctx after_explicit in

    let escaped_name = unique_name str in
    if replacements <> [] then
      Api_lp.register_explicit_replacements escaped_name replacements;
    let sym = add_constant ~impl escaped_name ty in
    { syms = [sym]; rules = []; }

  end else begin
    (* Has :args - need auxiliary symbol with rewrite rule *)

    (* Create context for encoding args - need all params *)
    let arg_ctx, _ = enc_params ps in

    (* Infer the type of each arg by encoding and using LambdaPi's type inference.
       We encode the arg term, then use Infer to get its type. *)
    let infer_arg_type arg =
      let encoded = enc_term ps arg_ctx arg |> resolve_term ~ctx:arg_ctx in
      match infer_type arg_ctx encoded with
      | Some ty -> un_tau ty
      | None -> failf "Cannot infer type of arg: %s" (Pp_eo.term_str arg)
    in

    (* Find parameters used in premises/conclusion but not in args.
       These are "extra" params (e.g. :premise-list variables) that must
       be added as explicit arguments to _aux so they appear in the LHS. *)
    let args_syms = EO.symbols_in_terms args in
    let rhs_syms = EO.symbols_in_terms (prems @ [conc]) in
    let param_names = List.map (fun (n, _, _) -> n) ps in
    let extra_params = List.filter (fun (n, _, _) ->
      EO.Set.mem n rhs_syms &&
      not (EO.Set.mem n args_syms) &&
      List.mem n param_names
    ) ps in
    (* Filter out Type params — they become implicit, not extra args *)
    let extra_params = List.filter (fun (_, ty, _) ->
      ty <> EO.Symbol EO.Builtin.ty_type) extra_params in

    let extra_lp_types = List.map (fun (_, ty, _) ->
      enc_term ps arg_ctx ty |> resolve_term ~ctx:arg_ctx) extra_params in
    let all_args = args @ List.map (fun (n, _, _) -> EO.Symbol n) extra_params in
    let arg_lp_types = List.map infer_arg_type args in
    let all_lp_types = arg_lp_types @ extra_lp_types in

    (* Build the _aux symbol type: τ T1 → τ T2 → ... → TYPE *)
    let aux_body_ty =
      List.fold_right
        (fun arg_ty acc ->
           let ty_enc = tau_of arg_ty in
           mk_Prod (ty_enc, bind_var (new_var "_") acc))
        all_lp_types
        (mk_Type)
    in

    (* Find implicit type params for _aux *)
    let aux_ty, aux_impl, aux_impl_ctx = impl_from_free_vars arg_ctx aux_body_ty in

    let aux_name = unique_name (str ^ "_aux") in
    let aux_sym = add_sequential ~impl:aux_impl aux_name aux_ty in

    (* Build the rewrite rule for _aux.
       LHS: (aux_name arg1 arg2 ... extra1 extra2 ...)
       RHS: Proof prem1 → ... → Proof conclusion *)

    (* Build LHS as an Eunoia Apply term *)
    let lhs_eo = EO.Apply (aux_name, all_args) in

    (* For RHS, we need to encode it specially since Proof is not in Eunoia.
       We'll encode the premises and conclusion, then build the arrow. *)
    let enc t = t
      |> enc_term ps arg_ctx
      |> resolve_term ~debug:!verbose ~ctx:arg_ctx ~expected_ty:tau_bool
      |> bind_pvars arg_ctx
    in

    let prems_enc = List.map enc prems in
    let conc_enc = enc conc in
    let rhs = build_proof_arrow prems_enc conc_enc in

    (* For LHS, use enc_case's encoding pattern *)
    let l = lhs_eo
      |> enc_term ps arg_ctx
      |> resolve_term ~debug:!verbose ~ctx:arg_ctx
      |> strip_eo_as
      |> bind_pvars arg_ctx
    in
    let _, lhs_args = Core.Term.get_args l in

    let aux_rule = mk_rule_record arg_ctx lhs_args rhs in

    (* Build the main symbol type:
       Π x1 : τ T1, ... Π xn : τ Tn, <name>_aux x1 ... xn *)

    (* Create fresh variables for the Π-bound args *)
    let arg_vars = List.mapi (fun i _ -> new_var (Printf.sprintf "x%d" (i + 1))) all_lp_types in

    (* Build _aux applied to implicit type params and then arg variables.
       Apply impl_ctx vars explicitly to avoid introducing placeholders. *)
    let aux_applied =
      let head =
        List.fold_left
          (fun acc (v, _, _) -> mk_Appl (acc, mk_Vari v))
          (mk_Symb aux_sym)
          (List.rev aux_impl_ctx)
      in
      List.fold_left
        (fun acc v -> mk_Appl (acc, mk_Vari v))
        head arg_vars
    in

    (* Build Π x1 : τ T1, ... Π xn : τ Tn, aux_applied *)
    let main_body_ty =
      List.fold_right2
        (fun arg_ty v acc ->
           let ty_enc = tau_of arg_ty in
           mk_Prod (ty_enc, bind_var v acc))
        all_lp_types arg_vars aux_applied
    in

    (* Find implicit type params for main symbol *)
    let main_ty, main_impl, _main_impl_ctx = impl_from_free_vars arg_ctx main_body_ty in

    let main_sym = add_constant ~impl:main_impl (unique_name str) main_ty in

    { syms = [aux_sym; main_sym];
      rules = [(aux_sym, aux_rule)]; }
  end

(* Encode an assume command.
   (assume s F) becomes: symbol s : Proof F; *)
let enc_assume str formula =
  let ctx = empty_ctxt in
  let formula_enc = enc_term [] ctx formula in
  let ty = mk_proof formula_enc in
  let sym = add_proof_constant (unique_name str) ty in
  { syms = [sym]; rules = []; }

(* Encode a step command.
   (step s F :rule r :premises (p1 ... pn) :args (a1 ... am))
   becomes: symbol s ≔ r a1 ... am p1 ... pn;
   Args precede premises to match the LP type signature produced by enc_rule. *)
let enc_step str rule_name premises args conc_opt =
  let ctx = empty_ctxt in
  let rule_sym = get_sym rule_name in
  let head = enc_sym rule_sym in
  (* Encode premises (which are proof term references) *)
  let prems_enc = List.map (fun p -> enc_term [] ctx p) premises in
  (* Check if the rule has :premise-list — if so, fold premises into a
     single conjunction proof using proof_cons/proof_nil.
     E.g. premises [p1; p2] become:
       proof_cons p1 (proof_cons p2 proof_nil)
     which has type Proof (and F1 (and F2 true)).
     LP infers the implicits when checking the generated file. *)
  let prems_enc, formula_enc =
    let rule_decl = Elab.find_all_eo_symbols rule_name
      |> List.find_map (fun (_, sym) ->
        match sym with EO.Rule (_, rdec) -> Some rdec | _ -> None)
    in
    match rule_decl with
    | Some { prem = Some (EO.PremiseList (_, op)); _ } ->
      let proof_nil_sym = get_sym "proof_nil" in
      let proof_cons_sym = get_sym "proof_cons" in
      (* Look up the operator's nil terminator *)
      let op_name = (match op with EO.Symbol s -> s | _ -> failf "premise-list op not a symbol") in
      let nil_term = match Elab.lookup_eo_symbol op_name with
        | Some (EO.Decl (_, _, Some (EO.RightAssocNil nil)))
        | Some (EO.Decl (_, _, Some (EO.RightAssocNilNSN nil))) -> nil
        | _ -> failf "premise-list op %s has no nil terminator" op_name
      in
      (* Build the conjunction formula from individual premise formulas.
         Each premise pi has type Proof(Fi); we infer Fi and fold:
         (op F1 (op F2 ... nil)) *)
      let op_enc = enc_term [] ctx op in
      let nil_enc = enc_term [] ctx nil_term in
      let premise_formulas = List.map (fun p ->
        (* Extract the formula from the premise's type: Proof F → F.
           Premises are symbol references; read sym_type directly
           instead of going through LP inference. *)
        let ty = match p with
          | Core.Term.Symb s -> Timed.(!(s.Core.Term.sym_type))
          | _ -> failf "premise-list: premise is not a symbol"
        in
        match ty with
        | Core.Term.Appl (Core.Term.Symb s, f)
          when s.Core.Term.sym_name = "Proof" -> f
        | _ -> failf "premise type is not Proof(...)"
      ) prems_enc in
      (* Fold formulas: (op F1 (op F2 ... nil)) *)
      let folded_formula = List.fold_right (fun f acc ->
        hol_app (hol_app op_enc f) acc
      ) premise_formulas nil_enc in
      (* Build the proof term: proof_cons p1 (proof_cons p2 ... proof_nil) *)
      let folded = List.fold_right (fun p acc ->
        add_args (enc_sym proof_cons_sym) [p; acc]
      ) prems_enc (enc_sym proof_nil_sym) in
      ([folded], [folded_formula])
    | Some { prem = Some (EO.Simple _); args; _ }
      when not (List.for_all (function EO.Symbol _ -> true | _ -> false) args) ->
      (* Simple premises on a rule with non-trivial :args (uses _aux path):
         extract each premise's formula from its type and pass them as
         explicit args so they participate in _aux pattern matching. *)
      let premise_formulas = List.map (fun p ->
        let ty = match p with
          | Core.Term.Symb s -> Timed.(!(s.Core.Term.sym_type))
          | _ -> failf "simple premise: premise is not a symbol"
        in
        match ty with
        | Core.Term.Appl (Core.Term.Symb s, f)
          when s.Core.Term.sym_name = "Proof" -> f
        | _ -> failf "simple premise type is not Proof(...)"
      ) prems_enc in
      (prems_enc, premise_formulas)
    | _ -> (prems_enc, [])
  in
  (* Encode args *)
  let args_enc = List.map (fun a -> enc_term [] ctx a) args in
  (* Build the full application.
     For :premise-list rules, the LP signature has the folded formula E
     as an explicit parameter (before :args and the proof). Insert it.
     For simple-premise rules, premise formulas precede :args. *)
  let body =
    let formula_args = formula_enc in
    let all_args = formula_args @ args_enc @ prems_enc in
    List.fold_left (fun acc arg -> mk_Appl (acc, arg)) head all_args
  in
  let expected_ty = match conc_opt with
    | Some conc ->
      let conc_enc = enc_term [] ctx conc in
      Some (mk_proof conc_enc)
    | None -> None
  in
  let sym = add_proof_definition (unique_name str) expected_ty body in
  { syms = [sym]; rules = []; }

let enc_symbol name = function
  | EO.Decl (ps, ty, attr) ->
    enc_decl name ps ty attr
  | EO.Defn (ps, body, ty_opt) ->
    enc_defn name ps body ty_opt
  | EO.Prog (ps, doms, ran, cases) ->
    enc_prog name ps doms ran cases
  | EO.Ltrl (cat, ty) ->
    enc_ltrl cat ty
  | EO.Rule (ps, rdec) ->
    enc_rule name ps rdec
  | EO.Assume formula ->
    enc_assume name formula
  | EO.AssumePush formula ->
    push_assumption formula;
    enc_assume name formula
  | EO.Step (rule_name, premises, args, conc_opt) ->
    enc_step name rule_name premises args conc_opt
  | EO.StepPop (rule_name, premises, args, conc_opt) ->
    let assm_formula = pop_assumption () in
    (* The assumption is now an explicit parameter in the rule's LP type,
       so pass it as the first arg (before :args) *)
    enc_step name rule_name premises (assm_formula :: args) conc_opt

(* Encode a single named symbol. Caller is responsible for
   calling reset_overloads() once before the first symbol in a module. *)
let enc_one (name : string) (sym : EO.symbol) : enc_result =
  set_current_symbol name;
  set_current_phase "encode";
  let r = enc_symbol name sym in
  set_current_symbol "";
  set_current_phase "";
  r
