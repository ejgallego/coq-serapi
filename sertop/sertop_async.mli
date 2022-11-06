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

(** [sertop fb_handler] Initialize Coq and send serialized feedback to
    [fb_handler] *)
val sertop_init :
  fb_out:(Sexp.t -> unit) ->
  ml_path:string list ->
  vo_path:Loadpath.vo_path list ->
  injections:Coqargs.injection_command list ->
  debug:bool ->
  set_impredicative_set:bool ->
  allow_sprop:bool ->
  Stm.doc * Stateid.t

(** [sertop_callback out input] Execute command [input] and send
    serialized output to [out]. Takes an internal mutex. *)
val sertop_callback : (Sexp.t -> unit) -> Sexp.t -> unit
