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

open Sexplib.Conv
open Ppx_python_runtime_serapi

module Names       = Ser_names
module Libnames    = Ser_libnames
module Constrexpr  = Ser_constrexpr
module Typeclasses = Ser_typeclasses
module Genarg      = Ser_genarg

type hint_db_name =
  [%import: Hints.hint_db_name]
  [@@deriving sexp,yojson]

type 'a hints_path_atom_gen =
  [%import: 'a Hints.hints_path_atom_gen]
  [@@deriving sexp,yojson]

type 'a hints_path_gen =
  [%import: 'a Hints.hints_path_gen]
  [@@deriving sexp,yojson]

type hints_path =
  [%import: Hints.hints_path]
  [@@deriving sexp,yojson]

(*
type reference_or_constr =
  [%import: Hints.reference_or_constr]
  [@@deriving sexp,yojson]
*)

type hint_mode =
  [%import: Hints.hint_mode]
  [@@deriving sexp,yojson,python]

(*
type hint_info_expr =
  [%import: Hints.hint_info_expr]
  [@@deriving sexp,yojson]
*)

type 'a hints_transparency_target =
  [%import: 'a Hints.hints_transparency_target]
  [@@deriving sexp,yojson,python]

(*
type hints_expr =
  [%import: Hints.hints_expr]
  [@@deriving sexp,yojson]
*)
