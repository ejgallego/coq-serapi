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

module Univ = Ser_univ

type family =
  [%import: Sorts.family]
  [@@deriving sexp,yojson,python]

type _t =
  | SProp
  | Prop
  | Set
  | Type of Univ.Universe.t
  [@@deriving sexp,yojson,python]

type t =
  [%import: Sorts.t]
  [@@deriving sexp_of,to_yojson,python_of]

let t_of_sexp x = Obj.magic (_t_of_sexp x)
let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= Obj.magic)
let t_of_python x = Obj.magic (_t_of_python x)

type relevance =
  [%import: Sorts.relevance]
  [@@deriving sexp,yojson,python]
