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

type t =
  [%import: CPrimitives.t]
  [@@deriving sexp,yojson]

type prim_type =
  [%import: CPrimitives.prim_type]
  [@@deriving sexp,yojson]

type op_or_type =
  [%import: CPrimitives.op_or_type]
  [@@deriving sexp,yojson]
