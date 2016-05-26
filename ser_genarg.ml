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

open Sexplib.Sexp

(**********************************************************************)
(* GenArg                                                             *)
(**********************************************************************)

open Genarg
type glob_generic_argument = [%import: Genarg.glob_generic_argument]

let glob_generic_argument_of_sexp _x = Obj.magic 0
let sexp_of_glob_generic_argument _x = Atom ""


