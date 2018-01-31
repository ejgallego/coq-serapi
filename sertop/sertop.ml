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

let sertop_version = "0.04dev"
let sertop printer print0 debug length prelude load_path rload_path implicit_prelude async async_full deep_edits  =

  (* Prepare load_paths by adding a boolean flag to mark -R or -Q *)
  let elp f = List.map (fun (l,d) -> l,d,f) in
  let loadpath = elp false load_path @ elp true rload_path in

  let open  Sertop_init         in
  let open! Sertop_sexp         in
  ser_loop
    {  in_chan  = stdin;
       out_chan = stdout;

       debug;
       printer;
       print0;
       lheader  = length;

       coqlib   = prelude;
       loadpath;
       std_impl = implicit_prelude;
       async = {
         enable_async = async;
         async_full = async_full;
         deep_edits = deep_edits;
       }
    }

let sertop_cmd =
  let open Sercmdopt in
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
