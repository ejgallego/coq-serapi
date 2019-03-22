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
(* Copyright 2016-2019 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let fatal_error msg =
  Format.eprintf "Error: @[%a@]@\n%!" Pp.pp_with msg;
  exit 1

let fatal_exn exn info =
  let loc = Loc.get_loc info in
  let exn, info = ExplainErr.process_vernac_interp_error (exn,info) in
  let msg = Pp.(pr_opt_no_spc Topfmt.pr_loc loc ++ fnl ()
                ++ CErrors.iprint (exn, info)) in
  fatal_error msg

let driver in_file coq_path =
  let open Sertop_init in

  (* coq initialization *)
  coq_init
    { fb_handler = (fun _ -> ())  (* XXXX *)
    ; ml_load    = None
    ; debug = true
    };

  Backtrace.record_backtrace true;

  (* We need to set the load path first to properly compute the lib
     name below *)
  let iload_path = Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path in
  List.iter Mltop.add_coq_path iload_path;

  (* The kernel replay needed this because our trace was too weak. *)
  (* let _dp = Library.start_library in_file in *)

  let in_chan = open_in in_file in
  try while true; do
      let line = input_line in_chan in
      if String.trim line <> "" then
        let sxp = Sexplib.Sexp.of_string line in
        let evt = Sercomp_ktrace.Event.t_of_sexp sxp in
        Sercomp_ktrace.replay evt
    done
  with End_of_file -> ();

open Cmdliner

let serload_version = Ser_version.ser_git_version

let serload_man =
  [ `S "DESCRIPTION"
  ; `P "Experimental Coq Kernel Trace replay module."
  ; `S "USAGE"
  ; `P "To load a kernel trace do:"
  ; `Pre "serload foo.ktrace"
  ]

let serload_doc = "sercomp Coq Compiler"

let main () =
  let input_file =
    let doc = "Input file." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:("FILE") ~doc)
  in

  let sercomp_cmd =
    let open Sertop_arg in
    Term.(const driver $ input_file $ prelude),
    Term.info "serload" ~version:serload_version ~doc:serload_doc ~man:serload_man
  in

  try match Term.eval ~catch:false sercomp_cmd with
    | `Error _ -> exit 1
    | _        -> exit 0
  with exn ->
    let (e, info) = CErrors.push exn in
    fatal_exn e info

let _ = main ()
