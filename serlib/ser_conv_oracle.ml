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
open Ppx_python_runtime

type level =
  [%import: Conv_oracle.level]
  [@@deriving sexp,yojson,python]

(* XXX: Fixme *)
type oracle =
  [%import: Conv_oracle.oracle]

let sexp_of_oracle = Serlib_base.sexp_of_opaque ~typ:"Conv_oracle.oracle"
let oracle_of_sexp _ = Conv_oracle.empty

let python_of_oracle = Serlib_base.python_of_opaque ~typ:"Conv_oracle.oracle"
let oracle_of_python _ = Conv_oracle.empty
