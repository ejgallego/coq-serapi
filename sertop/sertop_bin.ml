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

open Cmdliner

let sertop_version = Sertop.Ser_version.ser_git_version

let sertop printer print0 debug disallow_sprop indices_matter lheader coq_path ml_path no_init topfile no_prelude lp1 lp2 _std_impl async deep_edits async_workers error_recovery omit_loc omit_att omit_env exn_on_opaque =

  let open  Sertop.Sertop_init         in
  let open! Sertop.Sertop_sexp         in

  let options = Serlib.Serlib_init.{ omit_loc; omit_att; exn_on_opaque; omit_env } in
  Serlib.Serlib_init.init ~options;

  let dft_ml_path, vo_path =
    Serapi.Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path in
  let ml_path = dft_ml_path @ ml_path in
  let vo_path = vo_path @ lp1 @ lp2 in
  let allow_sprop = not disallow_sprop in

  ser_loop
    { in_chan  = stdin
    ; out_chan = stdout

    ; debug
    ; allow_sprop
    ; indices_matter
    ; printer
    ; print0
    ; lheader

    ; no_init
    ; no_prelude
    ; topfile
    ; ml_path
    ; vo_path
    ; async =
         { enable_async = async
         ; deep_edits
         ; async_workers
         ; error_recovery
       }
    }

let sertop_cmd =
  let open Sertop.Sertop_arg in
  let doc = "SerAPI Coq Toplevel" in
  let man = [
    `S "DESCRIPTION";
    `P "Experimental Coq Toplevel with Serialization Support";
    `S "USAGE";
    `P "To build a Coq document, use the `Add` command:";
    `Pre "(Add () \"Lemma addn0 n : n + 0. Proof. now induction n. Qed.\")";
    `P "SerAPI will parse and split the document into \"logical\" sentences.";
    `P "Then, you can ask Coq to check the proof with `Exec`:";
    `Pre "(Exec 5)";
    `P "Other queries are also possible; some examples:";
    `Pre "(Query ((sid 4)) Ast)";
    `P "Will print the AST at sentence 4.";
    `Pre "(Query ((sid 3)) Goals)";
    `P "Will print the goals at sentence 3.";
    `P "See the documentation on the project's webpage for more information"
  ]
  in
  Term.(const sertop
        $ printer $ print0 $ debug $ disallow_sprop $ indices_matter $ length $ prelude $ ml_include_path $ no_init $topfile $ no_prelude $ load_path $ rload_path $ implicit_stdlib
        $ async $ deep_edits $ async_workers $ error_recovery $ omit_loc $ omit_att $ omit_env $ exn_on_opaque ),
  Term.info "sertop" ~version:sertop_version ~doc ~man

let main () =
  match Term.eval sertop_cmd with
  | `Error _ -> exit 1
  | `Version
  | `Help
  | `Ok ()   -> exit 0

let _ = main ()
