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
module Names = Ser_names

type library_location =
  [%import: Loadpath.library_location]
  [@@deriving sexp]

type add_ml =
  [%import: Loadpath.add_ml]
  [@@deriving sexp]

type vo_path_spec =
  [%import: Loadpath.vo_path_spec]
  [@@deriving sexp]

type coq_path_spec =
  [%import: Loadpath.coq_path_spec]
  [@@deriving sexp]

type coq_path =
  [%import: Loadpath.coq_path]
  [@@deriving sexp]
