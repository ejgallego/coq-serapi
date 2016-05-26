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

type rlevel = [%import: Genarg.rlevel]
type glevel = [%import: Genarg.glevel]
type tlevel = [%import: Genarg.tlevel]

let rlevel_of_sexp _ = Obj.magic 0
let sexp_of_rlevel _ = Atom "GA_rlevel"

let glevel_of_sexp _ = Obj.magic 0
let sexp_of_glevel _ = Atom "GA_glevel"

let tlevel_of_sexp _ = Obj.magic 0
let sexp_of_tlevel _ = Atom "GA_tlevel"

type 'a generic_argument = [%import: 'a Genarg.generic_argument]

let generic_argument_of_sexp _ _x = Obj.magic 0
let sexp_of_generic_argument _ _x = Atom ""

type glob_generic_argument = [%import: Genarg.glob_generic_argument]
  [@@deriving sexp]

type raw_generic_argument  = [%import: Genarg.raw_generic_argument]
  [@@deriving sexp]

type typed_generic_argument  = [%import: Genarg.typed_generic_argument]
  [@@deriving sexp]

