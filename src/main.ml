(* main.ml
   eo2lp driver: translate Eunoia signatures to LambdaPi

   Pipeline stages:
   1. Parse all .eo files into a signature graph
   2. Initialize LambdaPi (prelude, package config)
   3. Encode all modules (encode → write .lp)
   4. Check all generated .lp files with LambdaPi
   5. Report results *)

open Syntax_eo

module Enc  = Encode
module LP   = Api_lp

(* ---------------------------------------------------------------------------
   CLI config
   --------------------------------------------------------------------------- *)

type config = {
  input_dir      : string;
  output_dir     : string;
  proofs_dir     : string option;
  check          : bool;
  timeout        : int;
  check_timeout  : int;
  log_level      : LP.log_level;
  no_color       : bool;
  include_expert : bool;
  step           : bool;
  bench          : bool;
  results_file   : string option;
}

let default_config = {
  input_dir      = "./cpc";
  output_dir     = "./_build/cpc";
  proofs_dir     = None;
  check          = false;
  timeout        = 0;
  check_timeout  = 0;
  log_level      = LP.Silent;
  no_color       = false;
  include_expert = false;
  step           = false;
  bench          = false;
  results_file   = None;
}

let config = ref default_config

let usage = "Usage: eo2lp [options]"

let speclist = [
  ("-d", Arg.String (fun s -> config := { !config with input_dir = s }),
   "<dir> Input directory with .eo files (default: ./cpc)");
  ("-o", Arg.String (fun s -> config := { !config with output_dir = s }),
   "<dir> Output directory for LambdaPi package (default: ./_build/cpc)");
  ("-v", Arg.String (fun s ->
     let level = LP.log_level_of_string s in
     config := { !config with log_level = level }),
   "<level> Log level: error, warn, info, debug");
  ("--proofs", Arg.String (fun s -> config := { !config with proofs_dir = Some s }),
   "<path> File or directory of .eo proof files to encode");
  ("--check", Arg.Unit (fun () -> config := { !config with check = true }),
   " Run lambdapi check on generated .lp files");
  ("--timeout", Arg.Int (fun n -> config := { !config with timeout = n }),
   "<sec> Encoding timeout per proof in seconds (default: 0 = no timeout)");
  ("--check-timeout", Arg.Int (fun n -> config := { !config with check_timeout = n }),
   "<sec> Lambdapi check timeout per proof in seconds (default: 0 = no timeout)");
  ("--no-color", Arg.Unit (fun () -> config := { !config with no_color = true }),
   " Disable colored output");
  ("--expert", Arg.Unit (fun () -> config := { !config with include_expert = true }),
   " Include files from expert/ directory");
  ("--step", Arg.Unit (fun () -> config := { !config with step = true }),
   " Print each proof step's EO source and generated LP in real time");
  ("--bench", Arg.Unit (fun () -> config := { !config with bench = true }),
   " Emit machine-readable per-proof lines to stderr for benchmarking");
  ("--results", Arg.String (fun s -> config := { !config with results_file = Some s }),
   "<file> Write per-proof results CSV to file");
]

(* Use centralized colors from Api_lp *)
let red    = LP.red
let green  = LP.green
let yellow = LP.yellow
let dim    = LP.dim

(* ---------------------------------------------------------------------------
   Helpers
   --------------------------------------------------------------------------- *)

let path_to_module pkg path = pkg ^ "." ^ String.concat "." path

let exn_msg = function
  | Failure msg -> msg
  | exn ->
    Printexc.to_string exn
    ^ (if Printexc.backtrace_status () then "\n" ^ Printexc.get_backtrace ()
       else "")

exception Timeout

(* Fork-based timeout: runs f() in a child process, kills it after secs.
   The child writes its result (error list) to a pipe; the parent reads it.
   If the child exceeds the timeout, the parent kills it and raises Timeout. *)
let with_timeout secs f =
  flush_all ();
  let pipe_r, pipe_w = Unix.pipe () in
  let pid = Unix.fork () in
  if pid = 0 then begin
    (* Child *)
    Unix.close pipe_r;
    let result = try f () with e -> [("(exception)", Printexc.to_string e)] in
    let oc = Unix.out_channel_of_descr pipe_w in
    Marshal.to_channel oc (result : (string * string) list) [];
    close_out oc;
    exit 0
  end else begin
    (* Parent *)
    Unix.close pipe_w;
    let timed_out = ref false in
    let old_handler = Sys.signal Sys.sigalrm
      (Sys.Signal_handle (fun _ -> timed_out := true)) in
    let old_alarm = Unix.alarm secs in
    let rec wait () =
      try Unix.waitpid [] pid
      with Unix.Unix_error (Unix.EINTR, _, _) ->
        if !timed_out then begin
          (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
          Unix.waitpid [] pid
        end else
          wait ()
    in
    let _, _status = wait () in
    ignore (Unix.alarm 0);
    Sys.set_signal Sys.sigalrm old_handler;
    if old_alarm > 0 then ignore (Unix.alarm old_alarm);
    if !timed_out then begin
      Unix.close pipe_r;
      raise Timeout
    end;
    let ic = Unix.in_channel_of_descr pipe_r in
    let result =
      try (Marshal.from_channel ic : (string * string) list)
      with _ -> [("(child)", "failed to read result from child process")]
    in
    close_in ic;
    result
  end

let fmt_time dt =
  if dt >= 10.0 then Printf.sprintf "%.1fs" dt
  else
    let ms = dt *. 1000. in
    if ms < 1.0 then dim "<1ms"
    else if ms < 10.0 then Printf.sprintf "%.1fms" ms
    else Printf.sprintf "%.0fms" ms

(* ---------------------------------------------------------------------------
   LambdaPi initialization
   --------------------------------------------------------------------------- *)

let clean_output_dir output_dir =
  if Sys.file_exists output_dir then begin
    let cmd = Printf.sprintf
      "find %s \\( -name '*.lpo' -o -name '*.lp' -o -name 'lambdapi.pkg' \\) -delete"
      (Filename.quote output_dir) in
    ignore (Sys.command cmd)
  end

let init_lambdapi ~output_dir ~pkg_name () =
  clean_output_dir output_dir;
  LP.mkdir_p output_dir;
  LP.generate_pkg_file output_dir pkg_name;
  LP.generate_prelude output_dir;
  let cwd = Sys.getcwd () in
  Sys.chdir output_dir;
  LP.init_library ();
  LP.apply_package_config ".";
  let prelude_path = [pkg_name; "Prelude"] in
  let sign = LP.compile prelude_path in
  Sys.chdir cwd;
  sign


(* ---------------------------------------------------------------------------
   Result types
   --------------------------------------------------------------------------- *)

type encode_result = {
  enc_errors   : (string * string) list;  (* (symbol_name, error_msg) *)
  enc_time     : float;
}

type check_outcome =
  | Check_ok
  | Check_error of string
  | Check_skipped of string

type module_result = {
  mod_path     : path;
  mod_name     : string;
  encode       : encode_result;
  check        : check_outcome;
  check_time   : float;
}

(* ---------------------------------------------------------------------------
   Shared encoding core: encode symbols, write .lp file, return errors
   --------------------------------------------------------------------------- *)

let encode_symbols ~pkg_name ~output_dir ~module_name ~mod_path
    ?(step=false) ~dep_modules (symbols : Syntax_eo.signature) =
  LP.set_current_module module_name;
  let debug = LP.log_level_geq LP.Debug in
  let trace = debug || step in

  let errors = ref [] in
  let output_items = ref [] in

  if trace then
    Printf.eprintf "\n%s\n  %s\n%s\n%!"
      (dim (String.make 72 '='))
      (String.concat "/" mod_path)
      (dim (String.make 72 '='));

  List.iter (fun (name, def) ->
    try
      if trace then
        Printf.eprintf "\n  %s\n%!" (dim (Pp_eo.symbol_str (name, def)));
      let result = Enc.enc_one name def in
      let item =
        { LP.oi_syms  = result.Enc.syms;
          oi_rules = result.Enc.rules; }
      in
      output_items := item :: !output_items;
      if trace then begin
        let lp_src = LP.render_item item in
        if lp_src <> "" then begin
          Printf.eprintf "  %s\n" (dim (String.make 40 '-'));
          String.split_on_char '\n' lp_src
          |> List.iter (fun line -> Printf.eprintf "  %s\n" line);
          flush stderr
        end
      end
    with e ->
      let msg = exn_msg e in
      errors := (name, msg) :: !errors
  ) symbols;

  let errors = List.rev !errors in

  (* Always write the .lp file with whatever succeeded *)
  let out_path =
    Filename.concat output_dir (String.concat "/" mod_path ^ ".lp")
  in
  LP.mkdir_p (Filename.dirname out_path);
  let prelude_module = pkg_name ^ ".Prelude" in
  LP.write_lp_file out_path ~prelude_module ~deps:dep_modules
    (List.rev !output_items);

  if trace && errors <> [] then
    List.iter (fun (sym, msg) ->
      Printf.eprintf "  %s %s\n%!"
        (red (Printf.sprintf "[%s:%s]" module_name sym)) msg
    ) errors;

  LP.set_current_module "";
  errors

(* ---------------------------------------------------------------------------
   Stage 3a: Encode a single module (elab → encode → write .lp)
   --------------------------------------------------------------------------- *)

let encode_module ~pkg_name ~output_dir
    (graph : sig_graph) (mod_path : path) =
  let node = PathMap.find mod_path graph in
  let deps = node.node_includes in
  let module_name = path_to_module pkg_name mod_path in

  let full_sig = full_sig_at graph mod_path in
  Enc.set_signature full_sig;

  let dep_paths = List.map (fun dep -> pkg_name :: dep) deps in
  let _sign = LP.init_sign ~deps:dep_paths (pkg_name :: mod_path) in
  Enc.reset_overloads ();

  let dep_modules = List.map (path_to_module pkg_name) deps in
  encode_symbols ~pkg_name ~output_dir ~module_name ~mod_path
    ~dep_modules node.node_sig

(* ---------------------------------------------------------------------------
   Stage 3b: Check a single module with LambdaPi
   --------------------------------------------------------------------------- *)

let check_module ?(timeout=30) ~output_dir (mod_path : path) =
  let rel_path = String.concat "/" mod_path ^ ".lp" in
  LP.check_file ~timeout output_dir rel_path

(* ---------------------------------------------------------------------------
   Stage 5: Encode a single proof file against the full CPC signature
   --------------------------------------------------------------------------- *)

let encode_proof ~pkg_name ~output_dir ~(top_module : path) ?(step=false)
    (name : string) (proof_sig : Syntax_eo.signature) =
  let proof_path = "proofs" :: String.split_on_char '/' name in
  let module_name = path_to_module pkg_name proof_path in

  Enc.set_signature_overlay proof_sig;

  let dep_path = pkg_name :: top_module in
  let _sign = LP.init_sign ~deps:[dep_path] (pkg_name :: proof_path) in
  Enc.reset_overloads ();
  Enc.reset_assumptions ();

  let dep_module = path_to_module pkg_name top_module in
  let errors =
    encode_symbols ~pkg_name ~output_dir ~module_name
      ~mod_path:proof_path ~step ~dep_modules:[dep_module] proof_sig
  in

  (* Validate assumption stack balance *)
  let stack_depth = Enc.assumption_stack_depth () in
  if stack_depth > 0 then
    errors @ [("(stack)", Printf.sprintf
      "assumption stack not empty after proof encoding (%d unpopped)" stack_depth)]
  else errors


(* ---------------------------------------------------------------------------
   Failure report: extract location, source line, and error body
   --------------------------------------------------------------------------- *)

(* Summarize verbose LP error messages into something human-readable.
   - "proof not finished" → extract [line:col], count of unfinished goals
   - long messages → truncate to max_len characters *)
let summarize_error ?(max_len=200) msg =
  let has s = try ignore (Str.search_forward (Str.regexp_string s) msg 0); true
              with Not_found -> false in
  if has "not finished" then begin
    (* Extract [line:col] location *)
    let loc =
      try
        let _ = Str.search_forward (Str.regexp "\\[\\([0-9]+\\):\\([0-9]+\\)\\]") msg 0 in
        Printf.sprintf "[%s:%s]" (Str.matched_group 1 msg) (Str.matched_group 2 msg)
      with Not_found -> "" in
    (* Count goals by counting " ≡ " occurrences *)
    let n_goals = ref 0 in
    let i = ref 0 in
    let eqv = "≡" in
    (try while true do
      let pos = Str.search_forward (Str.regexp_string eqv) msg !i in
      i := pos + String.length eqv;
      incr n_goals
    done with Not_found -> ());
    (* Extract the RHS of the first ≡ as a hint *)
    let hint =
      try
        let eqv_len = String.length eqv in
        let pos = Str.search_forward (Str.regexp_string eqv) msg 0 in
        let after = pos + eqv_len in
        (* Skip leading whitespace *)
        let start = ref after in
        while !start < String.length msg && msg.[!start] = ' ' do incr start done;
        (* Take until newline or next goal number *)
        let rest = String.sub msg !start (String.length msg - !start) in
        let rhs = try
          let nl = String.index rest '\n' in
          String.sub rest 0 nl
        with Not_found -> rest in
        let rhs = String.trim rhs in
        let rhs = if String.length rhs > 40 then String.sub rhs 0 40 ^ "..." else rhs in
        if rhs <> "" then Printf.sprintf " (... ≡ %s)" rhs else ""
      with Not_found -> "" in
    Printf.sprintf "%s proof not finished: %d goal(s)%s" loc !n_goals hint
  end
  else if String.length msg > max_len then
    String.sub msg 0 max_len ^ "..."
  else msg

let print_failure output_dir (name, phase, msg) =
  (* Convert module name cpc.programs.Foo to file path programs/Foo.lp *)
  let lp_path =
    match String.split_on_char '.' name with
    | _ :: rest ->
      Filename.concat output_dir (String.concat "/" rest ^ ".lp")
    | [] -> ""
  in
  let lines = String.split_on_char '\n' msg in
  let first_line = match lines with l :: _ -> l | [] -> msg in
  let body_lines = match lines with _ :: rest -> rest | [] -> [] in
  (* Try to extract a [line:col-col] location bracket *)
  let loc_source =
    try
      let _ = Str.search_forward
        (Str.regexp "\\(\\[[0-9][^]]*\\]\\)") first_line 0 in
      let loc = Str.matched_group 1 first_line in
      let line_num =
        let _ = Str.search_forward
          (Str.regexp "\\[\\([0-9]+\\):[0-9]") loc 0 in
        int_of_string (Str.matched_group 1 loc)
      in
      let source =
        try
          let ic = open_in lp_path in
          Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
            for _ = 1 to line_num - 1 do ignore (input_line ic) done;
            let line = String.trim (input_line ic) in
            let max_len = 72 in
            if String.length line > max_len
            then String.sub line 0 max_len ^ "..."
            else line)
        with _ -> ""
      in
      Some (loc, source)
    with Not_found -> None
  in
  Printf.printf "  %s: %s\n" (red name) (dim (Printf.sprintf "[%s]" phase));
  (match loc_source with
   | Some (loc, source) ->
     if source <> "" then
       Printf.printf "    %s %s\n" loc (dim source)
     else
       Printf.printf "    %s\n" loc;
     (* For "proof not finished" and other verbose errors, show a summary
        instead of dumping all body lines *)
     let summary = summarize_error msg in
     if summary <> msg then
       Printf.printf "    %s\n" summary
     else
       List.iter (fun l ->
         Printf.printf "      %s\n" l
       ) body_lines
   | None ->
     Printf.printf "    %s\n" (summarize_error first_line);
     if body_lines <> [] then
       List.iter (fun l ->
         let l = if String.length l > 80 then String.sub l 0 80 ^ "..." else l in
         Printf.printf "      %s\n" l
       ) body_lines)

(* ---------------------------------------------------------------------------
   Main entry point
   --------------------------------------------------------------------------- *)

let run () =
  Arg.parse speclist (fun _ -> ()) usage;

  (* --bench implies --check (benchmarking without verification is useless) *)
  if !config.bench then
    config := { !config with check = true };

  (* Apply global settings before any output *)
  LP.no_color := !config.no_color;
  LP.set_log_level !config.log_level;
  LP.verbose := LP.log_level_geq LP.Debug;
  (* Enable lambdapi SR debug logging *)
  if LP.log_level_geq LP.Debug then
    Common.Logger.set_debug true "s";

  let input_dir  = !config.input_dir in
  let output_dir = !config.output_dir in
  let pkg_name   = Filename.basename output_dir in

  (* -- Stage 1: Parse ---------------------------------------------------- *)

  let t0 = Unix.gettimeofday () in
  Printf.printf "parsing %s... " input_dir;
  flush stdout;
  let graph =
    Parse_eo.build_sig ~include_expert:!config.include_expert input_dir
  in
  (match Parse_eo.check_dag graph with
   | Ok () -> ()
   | Error cycle ->
     Printf.printf "%s\n" (red "FAIL");
     Printf.printf "  Cycle in include graph: %s\n"
       (String.concat " -> " (List.map path_str cycle));
     exit 1);
  Printf.printf "%s (%s)\n" (green "ok") (fmt_time (Unix.gettimeofday () -. t0));

  (* -- Stage 2: Initialize LambdaPi -------------------------------------- *)

  let t1 = Unix.gettimeofday () in
  Printf.printf "initializing lambdapi... ";
  flush stdout;
  let prelude_sign =
    init_lambdapi ~output_dir ~pkg_name () in
  LP.init prelude_sign;
  Printf.printf "%s (%s)\n"
    (green "ok") (fmt_time (Unix.gettimeofday () -. t1));

  (* Topological order for processing *)
  let order = topo_sort_graph graph in
  let total = List.length order in

  (* -- Stage 3: Encode all modules -------------------------------------- *)
  let t2 = Unix.gettimeofday () in
  Printf.printf "encoding %d modules... " total;
  flush stdout;

  let encode_results : (path * encode_result) list =
    List.map (fun mod_path ->
      let t_start = Unix.gettimeofday () in
      let errors =
        try encode_module ~pkg_name ~output_dir graph mod_path
        with e ->
          let name = path_to_module pkg_name mod_path in
          [("(module)", Printf.sprintf "%s: %s" name (exn_msg e))]
      in
      let enc = {
        enc_errors = errors;
        enc_time   = Unix.gettimeofday () -. t_start;
      } in
      (mod_path, enc)
    ) order
  in

  let encode_errs =
    List.filter (fun (_, enc) -> enc.enc_errors <> []) encode_results
  in
  let t_encode = Unix.gettimeofday () -. t2 in
  if encode_errs = [] then
    Printf.printf "%s (%s)\n" (green "ok") (fmt_time t_encode)
  else
    Printf.printf "%s %d/%d with errors (%s)\n"
      (red "WARN") (List.length encode_errs) total (fmt_time t_encode);

  (* -- Stage 4: Check all modules with LambdaPi (if --check) ------------ *)
  let results : module_result list =
    if !config.check then begin
      let t3 = Unix.gettimeofday () in
      Printf.printf "checking %d modules... " total;
      flush stdout;

      let results =
        List.map (fun (mod_path, enc) ->
          let mod_name = path_to_module pkg_name mod_path in
          let t_start = Unix.gettimeofday () in
          let r = check_module ~output_dir mod_path in
          let dt = Unix.gettimeofday () -. t_start in
          let check = match r with
            | LP.Check_ok    -> Check_ok
            | LP.Check_error msg -> Check_error msg
          in
          { mod_path; mod_name; encode = enc;
            check; check_time = dt }
        ) encode_results
      in

      let check_failures =
        List.filter (fun r ->
          match r.check with Check_error _ -> true | _ -> false) results
      in
      let t_check = Unix.gettimeofday () -. t3 in
      if check_failures = [] then
        Printf.printf "%s (%s)\n" (green "ok") (fmt_time t_check)
      else
        Printf.printf "%s %d/%d failed (%s)\n"
          (red "FAIL") (List.length check_failures) total (fmt_time t_check);
      results
    end else
      List.map (fun (mod_path, enc) ->
        let mod_name = path_to_module pkg_name mod_path in
        { mod_path; mod_name; encode = enc;
          check = Check_skipped "no --check"; check_time = 0.0 }
      ) encode_results
  in

  (* -- Stage 5: Encode and check proofs (if --proofs given) -------------- *)

  let proof_results : module_result list =
    match !config.proofs_dir with
    | None -> []
    | Some proofs_dir ->
      (* Find the top-level module (last in topo order) *)
      let top_module = List.rev order |> List.hd in
      (* Build the full CPC signature for proof encoding and snapshot
         the index so per-proof overlays avoid re-indexing ~1000 CPC symbols *)
      let cpc_sig = full_sig_at graph top_module in
      Enc.set_signature cpc_sig;
      Enc.snapshot_base_sig ();



      (* Parse proof files *)
      let t4 = Unix.gettimeofday () in
      let is_tty = Unix.isatty Unix.stdout in
      Printf.printf "parsing %d proofs... " 0;
      flush stdout;
      let parse_progress i total name =
        if is_tty then
          Printf.printf "\rparsing %d proofs... %s%s%!"
            total name (String.make (20 - min 20 (String.length name)) ' ')
        else ignore (i, name)
      in
      let proofs_raw =
        Parse_eo.parse_proof_dir ~progress:parse_progress proofs_dir in
      if is_tty then
        Printf.printf "\r%s\r%!" (String.make 72 ' ');
      let n_parse_errors =
        List.length (List.filter (fun (_, _, e) -> e > 0) proofs_raw) in
      if n_parse_errors > 0 then
        Printf.printf "\rparsing %d proofs... %s (%d with parse errors) (%s)\n"
          (List.length proofs_raw) (yellow "WARN") n_parse_errors
          (fmt_time (Unix.gettimeofday () -. t4))
      else
        Printf.printf "\rparsing %d proofs... %s (%s)\n"
          (List.length proofs_raw) (green "ok")
          (fmt_time (Unix.gettimeofday () -. t4));
      (* Filter out proofs with parse errors *)
      let proofs = List.filter_map (fun (name, sig_, errs) ->
        if errs > 0 then None else Some (name, sig_)
      ) proofs_raw in
      let n_proofs = List.length proofs in

      if n_proofs = 0 then []
      else begin
        let timeout = !config.timeout in
        (* Encode proofs *)
        let t5 = Unix.gettimeofday () in
        Printf.printf "encoding %d proofs... " n_proofs;
        flush stdout;

        let n_enc_err = ref 0 in

        let proof_encode_results =
          List.mapi (fun i (name, proof_sig) ->
            let t_start = Unix.gettimeofday () in
            let errors =
              try
                let step = !config.step in
                let do_enc () =
                  encode_proof ~pkg_name ~output_dir
                    ~top_module ~step name proof_sig in
                if timeout > 0 then with_timeout timeout do_enc
                else do_enc ()
              with
              | Timeout ->
                [("(timeout)", Printf.sprintf "encoding timed out (>%ds)" timeout)]
              | e ->
                let proof_path = "proofs" :: String.split_on_char '/' name in
                let mod_name = path_to_module pkg_name proof_path in
                [("(module)", Printf.sprintf "%s: %s" mod_name (exn_msg e))]
            in
            let sign_path = pkg_name :: "proofs" :: String.split_on_char '/' name in
            LP.reset_proof_state ~sign_path ();
            let dt = Unix.gettimeofday () -. t_start in
            let enc = { enc_errors = errors; enc_time = dt } in
            if errors <> [] then incr n_enc_err;
            if !config.bench then begin
              let ms = int_of_float (dt *. 1000.) in
              if errors = [] then
                Printf.eprintf "BENCH proof:%s encode ok %d\n%!" name ms
              else begin
                let _, first_msg = List.hd errors in
                let msg = String.split_on_char '\n' first_msg |> List.hd in
                Printf.eprintf "BENCH proof:%s encode error %d %s\n%!" name ms msg
              end
            end;
            if is_tty then begin
              let elapsed = Unix.gettimeofday () -. t5 in
              let rate = if elapsed > 0.0 then
                float_of_int (i + 1) /. elapsed else 0.0 in
              Printf.printf "\rencoding %d proofs... [%d/%d] (%.0f/s)%!"
                n_proofs (i + 1) n_proofs rate
            end;
            (name, enc)
          ) proofs
        in

        let t_penc = Unix.gettimeofday () -. t5 in
        if is_tty then Printf.printf "\r%s\rencoding %d proofs... %!"
          (String.make 72 ' ') n_proofs;
        if !n_enc_err = 0 then
          Printf.printf "%s (%s)\n" (green "ok") (fmt_time t_penc)
        else
          Printf.printf "%s %d/%d with errors (%s)\n"
            (yellow "WARN") !n_enc_err n_proofs (fmt_time t_penc);

        (* Check proofs (if --check) *)
        let proof_results =
          if !config.check then begin
            let timeout =
              if !config.check_timeout > 0 then !config.check_timeout
              else !config.timeout in
            let t6 = Unix.gettimeofday () in
            Printf.printf "checking %d proofs... " n_proofs;
            flush stdout;

            let n_chk_fail = ref 0 in

            let results =
              List.mapi (fun i (name, enc) ->
                let proof_path = "proofs" :: String.split_on_char '/' name in
                let mod_name = path_to_module pkg_name proof_path in
                let t_start = Unix.gettimeofday () in
                let check =
                  if enc.enc_errors <> [] then
                    Check_skipped "encode errors"
                  else
                    match check_module ~timeout ~output_dir proof_path with
                    | LP.Check_ok -> Check_ok
                    | LP.Check_error msg -> Check_error msg
                in
                let dt = Unix.gettimeofday () -. t_start in
                (match check with
                 | Check_ok -> ()
                 | Check_error _ | Check_skipped _ -> incr n_chk_fail);
                if !config.bench then begin
                  let ms = int_of_float (dt *. 1000.) in
                  match check with
                  | Check_ok ->
                    Printf.eprintf "BENCH proof:%s check ok %d\n%!" name ms
                  | Check_error msg ->
                    let line = String.split_on_char '\n' msg |> List.hd in
                    Printf.eprintf "BENCH proof:%s check error %d %s\n%!" name ms line
                  | Check_skipped reason ->
                    Printf.eprintf "BENCH proof:%s check skip %d %s\n%!" name ms reason
                end;
                if is_tty then begin
                  let elapsed = Unix.gettimeofday () -. t6 in
                  let rate = if elapsed > 0.0 then
                    float_of_int (i + 1) /. elapsed else 0.0 in
                  Printf.printf "\rchecking %d proofs... [%d/%d] (%.0f/s)%!"
                    n_proofs (i + 1) n_proofs rate
                end;
                { mod_path = proof_path; mod_name;
                  encode = enc; check; check_time = dt }
              ) proof_encode_results
            in

            let t_pchk = Unix.gettimeofday () -. t6 in
            if is_tty then Printf.printf "\r%s\rchecking %d proofs... %!"
              (String.make 72 ' ') n_proofs;
            if !n_chk_fail = 0 then
              Printf.printf "%s (%s)\n" (green "ok") (fmt_time t_pchk)
            else
              Printf.printf "%s %d/%d failed (%s)\n"
                (red "FAIL") !n_chk_fail n_proofs (fmt_time t_pchk);
            results
          end else
            List.map (fun (name, enc) ->
              let proof_path = "proofs" :: String.split_on_char '/' name in
              let mod_name = path_to_module pkg_name proof_path in
              { mod_path = proof_path; mod_name; encode = enc;
                check = Check_skipped "no --check"; check_time = 0.0 }
            ) proof_encode_results
        in

        proof_results
      end
  in

  (* -- Stage 6: Report --------------------------------------------------- *)

  let all_results = results @ proof_results in
  let all_total = List.length all_results in

  (* Collect all failures: encode errors + check errors *)
  let failures = ref [] in

  List.iter (fun r ->
    (* Report encode errors *)
    if r.encode.enc_errors <> [] then begin
      let first_sym, first_msg = List.hd r.encode.enc_errors in
      let msg =
        if List.length r.encode.enc_errors = 1 then
          Printf.sprintf "%s: %s" first_sym first_msg
        else
          Printf.sprintf "%s: %s (+%d more)"
            first_sym first_msg
            (List.length r.encode.enc_errors - 1)
      in
      failures := (r.mod_name, "encode", msg) :: !failures
    end;
    (* Report check errors *)
    (match r.check with
     | Check_error msg ->
       failures := (r.mod_name, "check", msg) :: !failures
     | _ -> ())
  ) all_results;

  let failures = List.rev !failures in
  let n_passed =
    List.length (List.filter (fun r ->
      r.encode.enc_errors = [] &&
      (match r.check with Check_ok | Check_skipped _ -> true | _ -> false)
    ) all_results)
  in
  let n_failed = all_total - n_passed in

  (* Summary line *)
  let status_str, status_color =
    if n_failed > 0 then ("FAIL", red) else ("OK", green)
  in
  Printf.printf "%s: %d passed" (status_color status_str) n_passed;
  if n_failed > 0 then Printf.printf ", %d failed" n_failed;
  Printf.printf "\n";

  (* Detailed failure output (cap at 20 for large proof sets) *)
  if failures <> [] then begin
    let max_detail = 20 in
    let shown = List.filteri (fun i _ -> i < max_detail) failures in
    List.iter (print_failure output_dir) shown;
    if List.length failures > max_detail then
      Printf.printf "  ... and %d more\n" (List.length failures - max_detail);
    let failed_names =
      List.filter_map (fun r ->
        if r.encode.enc_errors <> [] ||
           (match r.check with Check_error _ -> true | _ -> false)
        then Some (String.concat "/" r.mod_path)
        else None
      ) all_results
      |> List.sort_uniq String.compare
    in
    Printf.printf "Failed: %s\n" (String.concat ", " failed_names)
  end;

  (* Per-module detail at info level and above *)
  if LP.log_level_geq LP.Info then begin
    Printf.printf "\n%s\n" (dim "--- per-module detail ---");
    List.iter (fun r ->
      let status = match r.check with
        | Check_ok -> green "ok"
        | Check_error _ -> red "FAIL"
        | Check_skipped reason -> dim (Printf.sprintf "skip (%s)" reason)
      in
      Printf.printf "%s %s  enc %s  check %s\n"
        status r.mod_name (fmt_time r.encode.enc_time) (fmt_time r.check_time);
      if r.encode.enc_errors <> [] then
        List.iter (fun (sym, msg) ->
          Printf.printf "  ├─ %s %s\n" (red sym) msg
        ) r.encode.enc_errors
    ) all_results
  end;

  (* -- Write results CSV (if --results given) ----------------------------- *)

  (match !config.results_file with
   | None -> ()
   | Some csv_path ->
     let classify_error msg =
       let has s = try ignore (Str.search_forward (Str.regexp_string s) msg 0); true
                   with Not_found -> false in
       if has "timed out" || has "timeout" then "timeout"
       else if has "not finished" then "proof_not_finished"
       else if has "not found" || has "Not_found" then "symbol_not_found"
       else if has "unsupported literal" then "unsupported_literal"
       else if has "parse error" || has "Parse error" then "parse_error"
       else if has "pop_assumption" || has "assumption stack" then "stack_error"
       else if has "Cannot infer" || has "infer_noexn" then "type_inference"
       else if has "not in context" then "context_error"
       else if has "not unifiable" || has "Unification" then "unification"
       else if has "Subject" || has "subject" then "sr_failure"
       else if has "Typ" || has "typ" || has "type" then "type_error"
       else "other"
     in
     let escape_csv s =
       (* Replace newlines with spaces so CSV stays one-line-per-record *)
       let s = String.concat " " (String.split_on_char '\n' s) in
       if String.contains s ',' || String.contains s '"'
       then "\"" ^ String.concat "\"\"" (String.split_on_char '"' s) ^ "\""
       else s
     in
     let oc = open_out csv_path in
     Printf.fprintf oc "file,status,encode_time,check_time,error_category,error\n";
     List.iter (fun r ->
       (* Only write proof results, not CPC module results *)
       let is_proof = match r.mod_path with "proofs" :: _ -> true | _ -> false in
       if is_proof then begin
         let name = String.concat "/" r.mod_path in
         (* Strip leading "proofs/" prefix *)
         let name = match String.split_on_char '/' name with
           | "proofs" :: rest -> String.concat "/" rest
           | _ -> name
         in
         let status, error =
           if r.encode.enc_errors <> [] then
             let _, msg = List.hd r.encode.enc_errors in
             "fail_encode", msg
           else match r.check with
             | Check_error msg -> "fail_check", msg
             | Check_ok -> "pass", ""
             | Check_skipped reason -> "skip", reason
         in
         let error_cat = if error <> "" && status <> "skip"
                         then classify_error error else "" in
         let error = summarize_error ~max_len:150 error in
         Printf.fprintf oc "%s,%s,%.3f,%.3f,%s,%s\n"
           name status r.encode.enc_time r.check_time
           error_cat (escape_csv error)
       end
     ) all_results;
     close_out oc;
     Printf.printf "Results written to %s\n" csv_path
  );

  LP.reset ();
  if n_failed > 0 then exit 1;
  exit 0
