(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let fatal_error msg =
  Format.eprintf "Error: @[%a@]@\n%!" Pp.pp_with msg;
  exit 1

let fatal_exn exn info =
  let loc = Loc.get_loc info in
  let msg = Pp.(pr_opt_no_spc Topfmt.pr_loc loc ++ fnl ()
                ++ CErrors.iprint (exn, info)) in
  fatal_error msg

let create_document ~in_file ~async ~async_workers ~quick ~iload_path ~debug =

  let open Sertop_init in

  (* coq initialization *)
  coq_init
    { fb_handler = (fun _ -> ())  (* XXXX *)
    ; ml_load    = None
    ; debug
    };

  (* document initialization *)

  let stm_options = process_stm_flags
      { enable_async  = async
      ; async_full    = false
      ; deep_edits    = false
      ; async_workers = async_workers
      } in

  (* Disable due to https://github.com/ejgallego/coq-serapi/pull/94 *)
  let stm_options =
    { stm_options with
      async_proofs_tac_error_resilience = `None
    ; async_proofs_cmd_error_resilience = false
    } in

  let stm_options =
    if quick
    then { stm_options with async_proofs_mode = APonLazy }
    else stm_options
  in

  let require_libs = ["Coq.Init.Prelude", None, Some false] in

  let ndoc = { Stm.doc_type = Stm.VoDoc in_file
             ; require_libs
             ; iload_path
             ; stm_options
             } in

  (* Workaround, see
     https://github.com/ejgallego/coq-serapi/pull/101 *)
  if quick || async <> None
  then Safe_typing.allow_delayed_constants := true;

  Stm.new_doc ndoc

let input_doc ~input ~in_file ~in_chan ~process ~doc ~sid =
  let stt = ref (doc, sid) in
  let open Sertop_arg in
  match input with
  | I_vernac ->
     begin
       let in_strm = Stream.of_channel in_chan in
       let in_pa   = Pcoq.Parsable.make ~file:(Loc.InFile in_file) in_strm in
       try while true do
           let doc, sid = !stt in
           let east = Stm.parse_sentence ~doc sid in_pa in
           stt := process ~doc ~sid east
         done;
           fst !stt
       with Stm.End_of_input -> fst !stt
     end
  | I_sexp ->
     begin
       try while true; do
           let line = input_line in_chan in
           let doc, sid = !stt in
           if String.trim line <> "" then
             let sxp = Sexplib.Sexp.of_string line in
             let ast = Ser_cAst.t_of_sexp Ser_vernacexpr.vernac_control_of_sexp sxp in
             stt := process ~doc ~sid ast
         done;
           fst !stt
       with End_of_file -> fst !stt
     end

let process_vernac ~mode ~pp ~doc ~sid ast =
  let open Format in
  let doc, n_st, tip = Stm.add ~doc ~ontop:sid false ast in
  if tip <> `NewTip then
    fatal_error Pp.(str "fatal, got no `NewTip`");
  let open Sertop_arg in
  let () = match mode with
    | C_env   -> ()
    | C_vo    -> ()
    | C_check -> ()
    | C_parse -> ()
    | C_stats ->
      Sercomp_stats.do_stats ast
    | C_print ->
      printf "@[%a@]@\n%!" Pp.pp_with Ppvernac.(pr_vernac ast.v)
    | C_sexp ->
      printf "@[%a@]@\n%!" pp
        (Ser_cAst.sexp_of_t Ser_vernacexpr.sexp_of_vernac_control ast)
  in
  doc, n_st

let check_pending_proofs () =
  let pfs = Proof_global.get_all_proof_names () in
  if not CList.(is_empty pfs) then
    let msg = let open Pp in
      seq [ str "There are pending proofs: "
          ; pfs |> List.rev |> prlist_with_sep pr_comma Names.Id.print; str "."] in
    fatal_error msg

let close_document ~pp ~mode ~doc ~in_file =
  let open Sertop_arg in
  match mode with
  | C_parse -> ()
  | C_sexp  -> ()
  | C_print -> ()
  | C_stats ->
    Sercomp_stats.print_stats ()
  | C_check ->
    let _doc = Stm.join ~doc in
    check_pending_proofs ()
  | C_env ->
    let _doc = Stm.join ~doc in
    check_pending_proofs ();
    Format.printf "@[%a@]@\n%!" pp Ser_environ.(sexp_of_env Global.(env ()))
  | C_vo ->
    let _doc = Stm.join ~doc in
    check_pending_proofs ();
    let ldir = Stm.get_ldir ~doc in
    let out_vo = Filename.(remove_extension in_file) ^ ".vo" in
    Library.save_library_to ldir out_vo (Global.opaque_tables ())

(* Command line processing *)
let sercomp_version = Ser_version.ser_git_version

let sercomp_man =
  [
    `S "DESCRIPTION";
    `P "Experimental Coq compiler with serialization and deserialization support.";
    `S "USAGE";
    `P "To serialize `fs/fun.v` with logical path `Funs`:";
    `Pre "sercomp -Q fs,Funs --input=vernac --mode=sexp fs/fun.v > fs/fun.sexp";
    `P "To deserialize and check `fs/fun.sexp` with logical path `Funs`:";
    `Pre "sercomp -Q fs,Funs --input=sexp --mode=check fs/fun.sexp";
    `P "To generate `fs/fun.vo` from `fs/fun.sexp` with logical path `Funs`:";
    `Pre "sercomp -Q fs,Funs --input=sexp --mode=vo fs/fun.sexp";
    `P "See the documentation on the project's webpage for more information."
  ]

let sercomp_doc = "sercomp Coq Compiler"

open Cmdliner

let driver input mode debug printer async async_workers quick coq_path ml_path load_path rload_path in_file omit_loc omit_att exn_on_opaque =

  (* closures *)
  let pp = Sertop_ser.select_printer printer in
  let process = process_vernac ~mode ~pp in

  (* initialization *)
  let options = Serlib_init.{ omit_loc; omit_att; exn_on_opaque } in
  Serlib_init.init ~options;

  let iload_path = Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path @ ml_path @ load_path @ rload_path in
  let doc, sid = create_document ~in_file ~async ~async_workers ~quick ~iload_path ~debug in

  (* main loop *)
  let in_chan = open_in in_file in
  let doc = input_doc ~input ~in_file ~in_chan ~process ~doc ~sid in
  let () = close_document ~pp ~mode ~doc ~in_file in
  ()

let main () =
  let input_file =
    let doc = "Input file." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:("FILE") ~doc)
  in

  let sercomp_cmd =
    let open Sertop_arg in
    Term.(const driver
          $ comp_input $ comp_mode $ debug $ printer $ async $ async_workers $ quick $ prelude
          $ ml_include_path $ load_path $ rload_path $ input_file $ omit_loc $ omit_att $ exn_on_opaque
         ),
    Term.info "sercomp" ~version:sercomp_version ~doc:sercomp_doc ~man:sercomp_man
  in

  try match Term.eval ~catch:false sercomp_cmd with
    | `Error _ -> exit 1
    | _        -> exit 0
  with exn ->
    let (e, info) = CErrors.push exn in
    fatal_exn e info

let _ = main ()
