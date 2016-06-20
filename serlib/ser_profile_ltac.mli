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

type ltacprof_entry = Profile_ltac.ltacprof_entry

val ltacprof_entry_of_sexp : Sexp.t -> Profile_ltac.ltacprof_entry
val sexp_of_ltacprof_entry : Profile_ltac.ltacprof_entry -> Sexp.t

type ltacprof_tactic = Profile_ltac.ltacprof_tactic

val ltacprof_tactic_of_sexp : Sexp.t -> Profile_ltac.ltacprof_tactic
val sexp_of_ltacprof_tactic : Profile_ltac.ltacprof_tactic -> Sexp.t

type ltacprof_results = Profile_ltac.ltacprof_results

val ltacprof_results_of_sexp : Sexp.t -> Profile_ltac.ltacprof_results
val sexp_of_ltacprof_results : Profile_ltac.ltacprof_results -> Sexp.t

