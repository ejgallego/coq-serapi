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

type option_locality =
  [%import: Goptions.option_locality]
  [@@deriving sexp]

type option_name =
  [%import: Goptions.option_name]
  [@@deriving sexp]

type option_value =
  [%import: Goptions.option_value]
  [@@deriving sexp]

type option_state =
  [%import: Goptions.option_state]
  [@@deriving sexp]
