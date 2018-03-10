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

open Sexplib

val pp_sertop : Format.formatter -> Sexp.t -> unit

val coq_pp_opt : Pp.t -> Pp.t

val feedback_pos_filter : string -> Feedback.feedback -> Feedback.feedback

(* Optimizer/filter for feedback *)
type fb_filter_opts = {
  pp_opt : bool;
}

val default_fb_filter_opts : fb_filter_opts

val feedback_opt_filter : ?opts:fb_filter_opts -> Feedback.feedback -> Feedback.feedback option
