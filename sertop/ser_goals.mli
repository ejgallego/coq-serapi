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

open Sexplib

type goals_kind =
  | FgGoals
  | BgGoals
  | ShelvedGoals
  | GivenUpGoals

val goals_kind_of_sexp : Sexp.t -> goals_kind
val sexp_of_goals_kind : goals_kind -> Sexp.t

val get_goals : goals_kind -> (Richpp.richpp list * Constrexpr.constr_expr * string) list

