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

(** [sertop fb_handler] Initialize Coq and send feedback to [fb_handler] *)
val sertop_init : (Feedback.feedback -> unit) -> unit

(** [sertop_callback input out] Execute command [input] and send
    output to [out]. Not thread-safe. *)
val sertop_callback : Sexp.t -> (Sexp.t -> unit) -> unit
