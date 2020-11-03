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
open Sexplib.Std

type t =
  [%import: CPrimitives.t]
  [@@deriving sexp,yojson,python]

type const =
  [%import: CPrimitives.const]
  [@@deriving sexp,yojson,python]

(* XXX: GADTs ... *)
type 'a prim_type = [%import: 'a CPrimitives.prim_type]
and 'a prim_ind = [%import: 'a CPrimitives.prim_ind]
and ind_or_type = [%import: CPrimitives.ind_or_type]
  [@@deriving sexp_of]

let prim_type_of_sexp (x : Sexp.t) : 'a prim_type =
  match x with
  | Sexp.Atom "PT_int63" ->
    PT_int63
  | Sexp.Atom "PT_float64" ->
    PT_float64
  | Sexp.Atom "PT_array" ->
    Obj.magic PT_array
  | _ ->
    Sexplib.Conv_error.no_variant_match ()

type op_or_type = [%import: CPrimitives.op_or_type]
  [@@deriving sexp_of]

let op_or_type_of_sexp (x : Sexp.t) : op_or_type =
  match x with
  | Sexp.List [Sexp.Atom "OT_op"; p] ->
    OT_op (t_of_sexp p)
  | Sexp.List [Sexp.Atom "OT_type"; p] ->
    OT_type (prim_type_of_sexp p)
  | Sexp.List [Sexp.Atom "OT_const"; p] ->
    OT_const (const_of_sexp p)
  | _ ->
    Sexplib.Conv_error.no_variant_match ()

(* XXX *)
let op_or_type_to_yojson = Obj.magic
let op_or_type_of_yojson = Obj.magic

let python_of_op_or_type = Obj.magic
let op_or_type_of_python = Obj.magic
