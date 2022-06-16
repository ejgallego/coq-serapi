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

exception End_of_input

let input_doc ~input ~in_file ~in_chan ~process ~doc ~sid =
  let stt = ref (doc, sid) in
  let open Sertop.Sertop_arg in
  match input with
  | I_vernac ->
     begin
       let in_strm = Serapi.Ser_stream.of_channel in_chan in
       let in_pa   = Pcoq.Parsable.make ~loc:(Loc.initial (InFile { dirpath = None; file = in_file} )) in_strm in
       try while true do
           let doc, sid = !stt in
           let east =
             match Stm.parse_sentence ~doc ~entry:Pvernac.main_entry sid in_pa with
             | Some east -> east
             | None -> raise End_of_input in
           stt := process ~doc ~sid east
         done;
         !stt
       with End_of_input -> !stt
     end
  | I_sexp ->
     begin
       try while true; do
           let line = input_line in_chan in
           let doc, sid = !stt in
           if String.trim line <> "" then
             let sxp = Sexplib.Sexp.of_string line in
             let ast = Serlib.Ser_vernacexpr.vernac_control_of_sexp sxp in
             stt := process ~doc ~sid ast
         done;
         !stt
       with End_of_file -> !stt
     end

let process_vernac ~mode ~pp ~doc ~sid ast =
  let open Format in
  let doc, n_st, tip = Stm.add ~doc ~ontop:sid false ast in
  if tip <> NewAddTip then
    CErrors.user_err ?loc:ast.loc Pp.(str "fatal, got no `NewTip`");
  let open Sertop.Sertop_arg in
  let () = match mode with
    | C_env   -> ()
    | C_vo    -> ()
    | C_check -> ()
    | C_parse -> ()
    | C_stats ->
      Sertop.Sercomp_stats.do_stats ast
    | C_print ->
      printf "@[%a@]@\n%!" Pp.pp_with Ppvernac.(pr_vernac ast)
    | C_sexp ->
      printf "@[%a@]@\n%!" pp
        (Serlib.Ser_vernacexpr.sexp_of_vernac_control ast)
  in
  doc, n_st

let close_document ~pp ~mode ~doc ~in_file ~pstate =
  let open Sertop.Sertop_arg in
  match mode with
  | C_parse -> ()
  | C_sexp  -> ()
  | C_print -> ()
  | C_stats ->
    Sertop.Sercomp_stats.print_stats ()
  | C_check ->
    let _doc = Stm.join ~doc in
    Serapi.Serapi_doc.check_pending_proofs ~pstate
  | C_env ->
    let _doc = Stm.join ~doc in
    Serapi.Serapi_doc.check_pending_proofs ~pstate;
    Format.printf "@[%a@]@\n%!" pp Serlib.Ser_environ.(sexp_of_env Global.(env ()))
  | C_vo ->
    Serapi.Serapi_doc.save_vo ~doc ~pstate ~in_file ()

(* Command line processing *)
let sercomp_version = Sertop.Ser_version.ser_git_version

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

let driver input mode debug disallow_sprop indices_matter printer async async_workers error_recovery quick
    coq_path ml_path load_path rload_path in_file omit_loc omit_att omit_env exn_on_opaque =

  (* closures *)
  let pp = Sertop.Sertop_ser.select_printer printer in
  let process = process_vernac ~mode ~pp in

  (* initialization *)
  let doc, sid = Sertop.Comp_common.create_document
      ~debug ~disallow_sprop ~ml_path ~load_path ~rload_path ~quick ~in_file ~indices_matter
      ~omit_loc ~omit_att ~exn_on_opaque ~omit_env ~coq_path ~async ~async_workers ~error_recovery in

  (* main loop *)
  let in_chan = open_in in_file in
  let doc, _sid = input_doc ~input ~in_file ~in_chan ~process ~doc ~sid in
  let pstate = match Stm.state_of_id ~doc sid with
    | Valid (Some { Vernacstate.lemmas; _ }) -> lemmas
    | _ -> None
  in
  let () = close_document ~pp ~mode ~doc ~in_file ~pstate in
  ()

let main () =
  let input_file =
    let doc = "Input file." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:("FILE") ~doc)
  in

  let sercomp_cmd =
    let open Sertop.Sertop_arg in
    let term =
      Term.(const driver
            $ comp_input $ comp_mode $ debug $ disallow_sprop $ indices_matter $ printer $ async $ async_workers $ error_recovery $ quick $ prelude
            $ ml_include_path $ load_path $ rload_path $ input_file $ omit_loc $ omit_att $ omit_env $ exn_on_opaque
           ) in
    let info = Cmd.info "sercomp" ~version:sercomp_version ~doc:sercomp_doc ~man:sercomp_man in
    Cmd.v info term
  in

  try exit (Cmd.eval ~catch:false sercomp_cmd)
  with exn ->
    let (e, info) = Exninfo.capture exn in
    Sertop.Comp_common.fatal_exn e info

let _ = main ()
