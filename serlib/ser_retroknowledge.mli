(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)
open Sexplib

type retroknowledge = Retroknowledge.retroknowledge

val sexp_of_retroknowledge : retroknowledge -> Sexp.t
val retroknowledge_of_sexp : Sexp.t -> retroknowledge
val python_of_retroknowledge : retroknowledge -> Py.Object.t
val retroknowledge_of_python : Py.Object.t -> retroknowledge

type action = Retroknowledge.action

val sexp_of_action : action -> Sexp.t
val action_of_sexp : Sexp.t -> action
