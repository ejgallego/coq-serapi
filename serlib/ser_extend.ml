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

module Tok = Ser_tok

type side =
  [%import: Extend.side]
  [@@deriving sexp]

type gram_assoc =
  [%import: Extend.gram_assoc]
  [@@deriving sexp]

type gram_position =
  [%import: Extend.gram_position]
  [@@deriving sexp]

type production_position =
  [%import: Extend.production_position]
  [@@deriving sexp]

type production_level =
  [%import: Extend.production_level]
  [@@deriving sexp]

type ('lev,'pos) constr_entry_key_gen =
  [%import: ('lev, 'pos) Extend.constr_entry_key_gen]
  [@@deriving sexp]

type constr_entry_key =
  [%import: Extend.constr_entry_key]
  [@@deriving sexp]

type constr_prod_entry_key =
  [%import: Extend.constr_prod_entry_key]
  [@@deriving sexp]

type simple_constr_prod_entry_key =
  [%import: Extend.simple_constr_prod_entry_key]
  [@@deriving sexp]

