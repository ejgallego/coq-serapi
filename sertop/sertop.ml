(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let sertop_version = "0.04dev"

open Cmdliner

[@@@ocaml.warning "-44-45"]
let prelude =
  let doc = "Load Coq.Init.Prelude from $COQPATH; plugins/ and theories/ should live there." in
  Arg.(value & opt (some string) (Some Coq_config.coqlib) & info ["coqlib"] ~docv:"COQPATH" ~doc)

let async =
  let doc = "Enable async support using Coq binary $COQTOP (experimental)." in
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

let print_args = let open Sertop_sexp in
  Arg.(enum ["sertop", SP_Sertop; "human", SP_Human; "mach", SP_Mach])

let print_args_doc = Arg.doc_alts
  ["sertop, a custom printer (UTF-8 with emacs-compatible quoting)";
   "human, sexplib's human-format printer (recommended for debug sessions)";
   "mach, sexplib's machine-format printer"
  ]

let rload_path : (string * string) list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR" in
  Arg.(value & opt_all (pair dir string) [] & info ["R"; "rec-load-path"] ~docv:"DIR,LP"~doc)

let load_path : (string * string) list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR" in
  Arg.(value & opt_all (pair dir string) [] & info ["Q"; "load-path"] ~docv:"DIR,LP" ~doc)

let printer =
  let open Sertop_sexp in
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

let sertop printer print0 debug length prelude load_path rload_path implicit_prelude async async_full deep_edits  =

  (* Prepare load_paths by adding a boolean flag to mark -R or -Q *)
  let elp f = List.map (fun (l,d) -> l,d,f) in
  let loadpath = elp false load_path @ elp true rload_path in

  let open Sertop_init         in
  let open Sertop_sexp         in
  ser_loop
    {  in_chan  = stdin;
       out_chan = stdout;

       debug;
       printer;
       print0;
       lheader  = length;

       coqlib   = prelude;
       loadpath;
       implicit = implicit_prelude;
       async = {
         enable_async = async;
         async_full = async_full;
         deep_edits = deep_edits;
       }
    }

let sertop_cmd =
  let doc = "SerAPI Coq Toplevel" in
  let man = [
    `S "DESCRIPTION";
    `P "Experimental Coq Toplevel with serialization support"
  ]
  in
  Term.(const sertop
        $ printer $ print0 $ debug $ length $ prelude $ load_path $ rload_path $ implicit_stdlib
        $ async $ async_full $ deep_edits ),
  Term.info "sertop" ~version:sertop_version ~doc ~man

let main () =
  match Term.eval sertop_cmd with
  | `Error _ -> exit 1
  | _        -> exit 0

let _ = main ()
