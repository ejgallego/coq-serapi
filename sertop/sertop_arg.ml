(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Cmdliner

[@@@ocaml.warning "-44-45"]
let prelude =
  let doc = "Load Coq.Init.Prelude from $(docv); plugins/ and theories/ should live there." in
  Arg.(value & opt string Coq_config.coqlib & info ["coqlib"] ~docv:"COQPATH" ~doc)

let async =
  let doc = "Enable async support using Coq binary $(docv) (experimental)." in
  Arg.(value & opt (some string) None & info ["async"] ~doc ~docv:"COQTOP")

let async_full =
  let doc = "Enable Coq's async_full option." in
  Arg.(value & flag & info ["async-full"] ~doc)

let deep_edits =
  let doc = "Enable Coq's deep document edits option." in
  Arg.(value & flag & info ["deep-edits"] ~doc)

let implicit_stdlib =
  let doc = "Allow loading unqualified stdlib libraries (deprecated)." in
  Arg.(value & flag & info ["implicit"] ~doc)

let print_args = let open Sertop_ser in
  Arg.(enum ["sertop", SP_Sertop; "human", SP_Human; "mach", SP_Mach])

let print_args_doc = Arg.doc_alts
  ["sertop, a custom printer (UTF-8 with emacs-compatible quoting)";
   "human, sexplib's human-format printer (recommended for debug sessions)";
   "mach, sexplib's machine-format printer"
  ]

let printer =
  let open Sertop_ser in
  (* XXX Must improve argument information *)
  (* let doc = "Select S-expression printer." in *)
  Arg.(value & opt print_args SP_Sertop & info ["printer"] ~doc:print_args_doc)

let debug =
  let doc = "Enable debug mode for Coq." in
  Arg.(value & flag & info ["debug"] ~doc)

let print0 =
  let doc = "End responses with a \\\\0 char." in
  Arg.(value & flag & info ["print0"] ~doc)

let length =
  let doc = "Emit a byte-length header before output. (deprecated)." in
  Arg.(value & flag & info ["length"] ~doc)

(* We handle the conversion here *)
open Sertop_init

let coq_lp_conv ~implicit (dir,lp) = {
  coq_path  = Libnames.dirpath_of_string lp;
  unix_path = dir;
  has_ml    = true;
  recursive = true;
  implicit;
}

let rload_path : load_path_spec list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR and implicitly open its namespace." in
  Term.(const List.(map (coq_lp_conv ~implicit:true)) $
        Arg.(value & opt_all (pair dir string) [] & info ["R"; "rec-load-path"] ~docv:"DIR,LP"~doc))

let load_path : load_path_spec list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR" in
  Term.(const List.(map (coq_lp_conv ~implicit:false)) $
        Arg.(value & opt_all (pair dir string) [] & info ["Q"; "load-path"] ~docv:"DIR,LP" ~doc))


(* Low-level serialization options for display *)
let omit_loc : bool Term.t =
  let doc = "[debug option] shorten location printing" in
  Arg.(value & flag & info ["omit_loc"] ~doc)

let omit_att : bool Term.t =
  let doc = "[debug option] omit attribute nodes" in
  Arg.(value & flag & info ["omit_att"] ~doc)
