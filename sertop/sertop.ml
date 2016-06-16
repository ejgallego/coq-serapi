(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let sertop_version = "0.03dev"

open Cmdliner

let prelude =
  let doc = "Load prelude from COQPATH; plugins/ and theories/ should live there." in
  Arg.(value & opt (some string) Coq_config.coqlib & info ["prelude"] ~docv:"COQPATH" ~doc)

let async =
  let doc = "Enables async support with toplevel COQTOP (experimental)." in
  Arg.(value & opt (some string) None & info ["async"] ~doc ~docv:"COQTOP")

let async_full =
  let doc = "Enable async_full in the STM." in
  Arg.(value & flag & info ["async-full"] ~doc)

let deep_edits =
  let doc = "Enable deep edits into the document." in
  Arg.(value & flag & info ["deep-edits"] ~doc)

let human =
  let doc = "Use human-readable sexp output." in
  Arg.(value & flag & info ["human"] ~doc)

let print0 =
  let doc = "Add a \\\\0 char after every response." in
  Arg.(value & flag & info ["print0"] ~doc)

let length =
  let doc = "Adds a byte-length header to answers." in
  Arg.(value & flag & info ["length"] ~doc)


let sertop prelude human print0 length async async_full deep_edits =
  let open Sertop_init             in
  let open Sertop_protocol         in
  ser_loop
    {  coqlib   = prelude;
       in_chan  = stdin;
       out_chan = stdout;
       human    = human;
       print0   = print0;
       lheader  = length;
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
  Term.(const sertop $ prelude $ human $ print0 $ length $ async $ async_full $ deep_edits ),
  Term.info "sertop" ~version:sertop_version ~doc ~man

let main () =
  match Term.eval sertop_cmd with
  | `Error _ -> exit 1
  | _        -> exit 0

let _ = main ()
