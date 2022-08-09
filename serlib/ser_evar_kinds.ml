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

module Names     = Ser_names
module Evar      = Ser_evar
module Constr    = Ser_constr

(**********************************************************************)
(* Evar_kinds                                                         *)
(**********************************************************************)

type matching_var_kind =
  [%import: Evar_kinds.matching_var_kind]
  [@@deriving sexp,yojson,python,hash,compare]

type obligation_definition_status =
  [%import: Evar_kinds.obligation_definition_status]
  [@@deriving sexp,yojson,python,hash,compare]

type record_field =
  [%import: Evar_kinds.record_field]
  [@@deriving sexp,yojson,python,hash,compare]

type question_mark =
  [%import: Evar_kinds.question_mark]
  [@@deriving sexp,yojson,python,hash,compare]

type subevar_kind =
  [%import: Evar_kinds.subevar_kind]
  [@@deriving sexp,yojson,python,hash,compare]

type t =
  [%import: Evar_kinds.t]
  [@@deriving sexp,yojson,python,hash,compare]
