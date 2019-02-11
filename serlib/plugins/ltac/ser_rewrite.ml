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

type unary_strategy =
  [%import: Ltac_plugin.Rewrite.unary_strategy]
  [@@deriving sexp]

type binary_strategy =
  [%import: Ltac_plugin.Rewrite.binary_strategy]
  [@@deriving sexp]

type ('a,'b) strategy_ast =
  [%import: ('a,'b) Ltac_plugin.Rewrite.strategy_ast]
  [@@deriving sexp]
