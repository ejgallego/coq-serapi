(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_python_runtime
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Libnames = Ser_libnames

type option_locality =
  [%import: Goptions.option_locality]
  [@@deriving sexp,yojson,python]

type option_name =
  [%import: Goptions.option_name]
  [@@deriving sexp,yojson,python,hash,compare]

type option_value =
  [%import: Goptions.option_value]
  [@@deriving sexp,yojson,python,hash,compare]

type option_state =
  [%import: Goptions.option_state]
  [@@deriving sexp,yojson,python,hash,compare]

type table_value =
  [%import: Goptions.table_value]
  [@@deriving sexp,yojson,python,hash,compare]

