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
(* Copyright 2019-2022 Inria                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_python_runtime

module Nametab = Ser_nametab
module Libobject = Ser_libobject
module Summary = Ser_summary

type is_type =
  [%import: Lib.is_type]
  [@@deriving sexp,python]

type export_flag =
  [%import: Lib.export_flag]
  [@@deriving sexp,python]

type export =
  [%import: Lib.export]
  [@@deriving sexp,python]

type node =
  [%import: Lib.node]
  [@@deriving sexp,python]

type library_segment =
  [%import: Lib.library_segment]
  [@@deriving sexp,python]
