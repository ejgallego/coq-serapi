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
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib
open Ssrmatching_plugin

type cpattern =
  [%import: Ssrmatching.cpattern]

let cpattern_of_sexp x = Obj.magic x
let sexp_of_cpattern _x = Sexp.Atom "XXX cpattern"

type rpattern =
  [%import: Ssrmatching.rpattern]

let rpattern_of_sexp x = Obj.magic x
let sexp_of_rpattern _x = Sexp.Atom "XXX cpattern"

type ssrdir =
  [%import: Ssrmatching.ssrdir]
  [@@deriving sexp]
