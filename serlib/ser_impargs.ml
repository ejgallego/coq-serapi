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
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Names = Ser_names
module Constrexpr = Ser_constrexpr

type argument_position =
  [%import: Impargs.argument_position]
  [@@deriving sexp,python]

type implicit_explanation =
  [%import: Impargs.implicit_explanation]
  [@@deriving sexp,python]

type maximal_insertion =
  [%import: Impargs.maximal_insertion]
  [@@deriving sexp,python]

type force_inference =
  [%import: Impargs.force_inference]
  [@@deriving sexp,python]

module ISCPierceSpec = struct
  type t = Impargs.implicit_side_condition
  type _t = DefaultImpArgs | LessArgsThan of int
  [@@deriving sexp,yojson,python,hash,compare]
end

module B_ = SerType.Pierce(ISCPierceSpec)
type implicit_side_condition = B_.t
let sexp_of_implicit_side_condition = B_.sexp_of_t
let implicit_side_condition_of_sexp = B_.t_of_sexp
let python_of_implicit_side_condition = B_.python_of_t
let implicit_side_condition_of_python = B_.t_of_python
let implicit_side_condition_of_yojson = B_.of_yojson
let implicit_side_condition_to_yojson = B_.to_yojson
let hash_implicit_side_condition = B_.hash
let hash_fold_implicit_side_condition = B_.hash_fold_t
let compare_implicit_side_condition = B_.compare

type implicit_position =
  [%import: Impargs.implicit_position]
  [@@deriving sexp,python]

type implicit_status =
  [%import: Impargs.implicit_status]
  [@@deriving sexp,python]

type implicits_list =
  [%import: Impargs.implicits_list]
  [@@deriving sexp,python]
