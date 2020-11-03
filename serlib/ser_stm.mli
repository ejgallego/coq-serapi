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

(* type interactive_top = Stm.interactive_top
 *
 * val sexp_of_interactive_top : Stm.interactive_top -> Sexp.t
 * val interactive_top_of_sexp : Sexp.t -> Stm.interactive_top
 * val python_of_interactive_top : Stm.interactive_top -> Py.Object.t
 * val interactive_top_of_python : Py.Object.t -> Stm.interactive_top *)

type focus = Stm.focus

val sexp_of_focus : Stm.focus -> Sexp.t
val focus_of_sexp : Sexp.t -> Stm.focus
