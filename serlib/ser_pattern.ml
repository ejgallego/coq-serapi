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

module Names     = Ser_names
module Globnames = Ser_globnames
module Term      = Ser_constr
module Misctypes = Ser_misctypes

type case_info_pattern =
  [%import: Pattern.case_info_pattern]
  [@@deriving sexp]

type constr_pattern =
  [%import: Pattern.constr_pattern]
  [@@deriving sexp]
