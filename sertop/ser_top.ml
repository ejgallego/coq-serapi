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

open Sexplib
(* Write the protocol handler *)

type command = int
type answer  = int
type query   = int

let parse_command () = ()
let do_command    old_state _cmd = old_state
let print_answers () = ()

let fb_handler fb =
  Format.printf "%a@\n%!" Ser_top_util.pp_feedback fb;
  let ser_fb = Ser_feedback.sexp_of_feedback fb   in
  Format.printf "%a@\n%!" Sexp.pp_hum ser_fb

(* Switch to a reactive lib? *)
let verb = true

let rec loop old_state =
  (* Parsing *)
  try
    let new_state, _ = Stm.add ~ontop:old_state verb 0 (read_line ()) in
    (* Execution *)
    begin try
        Stm.finish ();
        loop new_state
      (* Execution error *)
      with exn ->
        Format.eprintf "%a@\n%!" Sexp.pp_hum (Conv.sexp_of_exn exn);
        ignore (Stm.edit_at old_state);
        loop old_state
    end
  with
  (* End of input *)
  | End_of_file -> old_state
  (* Parse error *)
  | exn ->
    Format.eprintf "%a@\n%!" Sexp.pp_hum (Conv.sexp_of_exn exn);
    loop old_state

let main () =
  let istate = Ser_init.coq_init { Ser_init.fb_handler = fb_handler; } in
  Format.printf "Coq initialized with state: %s\n" (Stateid.to_string istate);
  Format.printf "Coq      exited with state: %s\n" (Stateid.to_string (loop istate));
  ()

let _ =
  let _u = Ser_protocol.Summary in
  main ()
