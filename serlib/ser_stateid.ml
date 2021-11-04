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

open Sexplib.Std
open Ppx_python_runtime_serapi

type t =
  [%import: Stateid.t]

type _t = int [@@deriving sexp, yojson, python]

let _t_put stateid = (Stateid.to_int stateid)
let _t_get stateid = Stateid.of_int stateid

let t_of_sexp sexp    = _t_get (_t_of_sexp sexp)
let sexp_of_t stateid = sexp_of__t (_t_put stateid)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

let t_of_python python    = _t_get (_t_of_python python)
let python_of_t stateid = python_of__t (_t_put stateid)
