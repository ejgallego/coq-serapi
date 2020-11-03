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

type level =
  [%import: Conv_oracle.level]
  [@@deriving sexp,yojson,python,hash,compare]

module OpaqueOracle = struct
  type t = Conv_oracle.oracle
  let name = "Conv_oracle.oracle"
end

module B = SerType.Opaque(OpaqueOracle)

type oracle = B.t
let sexp_of_oracle = B.sexp_of_t
let oracle_of_sexp = B.t_of_sexp
let python_of_oracle = B.python_of_t
let oracle_of_python = B.t_of_python
let oracle_of_yojson = B.of_yojson
let oracle_to_yojson = B.to_yojson
let hash_oracle = B.hash
let hash_fold_oracle = B.hash_fold_t
let compare_oracle = B.compare
