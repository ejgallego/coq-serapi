(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib
open Ppx_python_runtime

type _t = string [@@deriving yojson,python]
let _t_put = Uint63.to_string
let _t_get x = Uint63.of_int64 (Int64.of_string x)

type t = Uint63.t

let t_of_sexp (x : Sexp.t) : Uint63.t = _t_get (Conv.string_of_sexp x)
let sexp_of_t (x : Uint63.t) : Sexp.t = Conv.sexp_of_string (_t_put x)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

let t_of_python (x : Py.Object.t) : Uint63.t = _t_get (_t_of_python x)
let python_of_t (x : Uint63.t) : Py.Object.t = python_of__t (_t_put x)
