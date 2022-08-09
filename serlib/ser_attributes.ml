(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2020 MINES ParisTech / INRIA                          *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_python_runtime
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module CAst = Ser_cAst

type vernac_flag_type =
  [%import: Attributes.vernac_flag_type]
  [@@deriving sexp,yojson,python,hash,compare]

type vernac_flag =
  [%import: Attributes.vernac_flag]
and vernac_flag_value =
  [%import: Attributes.vernac_flag_value]
and vernac_flags =
  [%import: Attributes.vernac_flags]
  [@@deriving sexp,yojson,python,hash,compare]
