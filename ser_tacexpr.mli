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

type raw_tactic_expr = Tacexpr.raw_tactic_expr

val raw_tactic_expr_of_sexp : Sexp.t -> raw_tactic_expr
val sexp_of_raw_tactic_expr : raw_tactic_expr -> Sexp.t

type raw_red_expr = Tacexpr.raw_red_expr

val raw_red_expr_of_sexp : Sexp.t -> raw_red_expr
val sexp_of_raw_red_expr : raw_red_expr -> Sexp.t
