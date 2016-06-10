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

(* XXX: Parse command line *)
let prelude = ref None
let human   = ref false

let ser_usage = "Usage: ser_top [options] inputfile"

let ser_arg   = [
  "-prelude", Arg.String (fun l -> prelude := Some l),
        "Load prelude from dir";
  "-human",   Arg.Unit   (fun _ -> human   := true),
        "Use human-readable sexp output";
]

let parse_args () =
  let in_files = ref [] in
  Arg.parse ser_arg
     (fun file -> in_files := file :: !in_files)
     ser_usage;
  List.rev !in_files

let main () =
  let open Sertop_protocol         in
  let _  = parse_args ()           in
  ser_loop
    {  coqlib   = !prelude;
       in_chan  = stdin;
       out_chan = stdout;
       human    = !human;
    }

let _ =
  main ()
