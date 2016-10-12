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

module Names      = Ser_names
module Constrexpr = Ser_constrexpr
module Tok        = Ser_tok
module Extend     = Ser_extend

type grammar_constr_prod_item =
  [%import: Notation_term.grammar_constr_prod_item]
  [@@deriving sexp]

type notation_var_internalization_type =
  [%import: Notation_term.notation_var_internalization_type]
  [@@deriving sexp]

type notation_grammar =
  [%import: Notation_term.notation_grammar]
  [@@deriving sexp]

