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

(* Main protocol handler *)

(* Write the protocol handler *)

type command = int
type answer  = int
type query   = int

let parse_command () = ()
let do_command    old_state _cmd = old_state
let print_answers () = ()

let fb_handler _ = ()

(* Switch to a reactive lib? *)
let rec loop old_state =
  let new_state = do_command old_state (parse_command ()) in
  print_answers ();
  loop new_state

let main () =
  let istate = Ser_init.coq_init { Ser_init.fb_handler = fb_handler; } in
  Format.printf "Coq initialized with state: %s\n" (Stateid.to_string istate);
  (* ignore (loop istate) *)
  ()

let _ = main ()
