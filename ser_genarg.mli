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

(**********************************************************************)
(* GenArg                                                             *)
(**********************************************************************)


type glob_generic_argument = Genarg.glob_generic_argument

val glob_generic_argument_of_sexp : Sexp.t -> Genarg.glob_generic_argument
val sexp_of_glob_generic_argument : Genarg.glob_generic_argument -> Sexp.t
