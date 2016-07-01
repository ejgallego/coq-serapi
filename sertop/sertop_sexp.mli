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
open Sertop_protocol

(* Sexp-serialization of the protocol *)

val coq_object_of_sexp : Sexp.t -> coq_object
val sexp_of_coq_object : coq_object -> Sexp.t

val print_format_of_sexp : Sexp.t -> print_format
val sexp_of_print_format : print_format -> Sexp.t

val print_opt_of_sexp : Sexp.t -> print_opt
val sexp_of_print_opt : print_opt -> Sexp.t

val sexp_of_answer_kind : answer_kind -> Sexp.t
val answer_kind_of_sexp : Sexp.t -> answer_kind

val sexp_of_control_cmd : control_cmd -> Sexp.t
val control_cmd_of_sexp : Sexp.t -> control_cmd

val query_pred_of_sexp : Sexp.t -> query_pred
val sexp_of_query_pred : query_pred -> Sexp.t

val query_opt_of_sexp : Sexp.t -> query_opt
val sexp_of_query_opt : query_opt -> Sexp.t

val query_cmd_of_sexp : Sexp.t -> query_cmd
val sexp_of_query_cmd : query_cmd -> Sexp.t

val cmd_of_sexp : Sexp.t -> cmd
val sexp_of_cmd : cmd -> Sexp.t

val tagged_cmd_of_sexp : Sexp.t -> tagged_cmd
val sexp_of_tagged_cmd : tagged_cmd -> Sexp.t

val sexp_of_answer : answer -> Sexp.t
val answer_of_sexp : Sexp.t -> answer

(******************************************************************************)
(* Global Protocol Options                                                    *)
(******************************************************************************)

type ser_opts = {
  coqlib   : string option;       (* Whether we should load the prelude, and its location *)
  in_chan  : in_channel;          (* Input/Output channels                                *)
  out_chan : out_channel;
  human    : bool;                (* Output function to use                               *)
  print0   : bool;
  lheader  : bool;
  implicit : bool;
  async    : Sertop_init.async_flags;
}

(******************************************************************************)
(* Input/Output -- Main Loop                                                  *)
(******************************************************************************)

(** [ser_loop opts] main se(xp)r-protocol loop *)
val ser_loop : ser_opts -> unit
