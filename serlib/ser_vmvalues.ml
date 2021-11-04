(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv
open Ppx_python_runtime_serapi

module Sorts = Ser_sorts
module Names = Ser_names
module Univ  = Ser_univ
module Uint63 = Ser_uint63
module Float64 = Ser_float64

type tag =
  [%import: Vmvalues.tag]
  [@@deriving sexp,python]

type structured_values = Vmvalues.structured_values

let structured_values_of_sexp _ = assert false
let sexp_of_structured_values _ = assert false
let structured_values_of_python _ = assert false
let python_of_structured_values _ = assert false

type structured_constant =
  [%import: Vmvalues.structured_constant]
  [@@deriving sexp,python]

type reloc_table =
  [%import: Vmvalues.reloc_table]
  [@@deriving sexp,python]

type annot_switch =
  [%import: Vmvalues.annot_switch]
  [@@deriving sexp,python]
