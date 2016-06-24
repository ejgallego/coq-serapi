(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API -- Async loop                                  *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib
open Sertop_async

(* Send answer to the main thread *)
let post_message (msg : Sexp.t) : unit =
  let msg_str = Js.string (Sexp.to_string msg) in
  Worker.post_message msg_str

(* Receive message from the main thread *)
let on_message (cmd : Sexp.t) : unit =
  sertop_callback cmd post_message

(* This code is executed on Worker initialization *)
let _ =
  let on_msg str =
    try
      let cmd = Sexp.of_string (Js.to_string str) in
      on_message cmd
    with _ ->
      Worker.post_message (Js.string "Error in input conversion")
  in
  Worker.set_onmessage on_msg;
  sertop_init post_message;
  ()
