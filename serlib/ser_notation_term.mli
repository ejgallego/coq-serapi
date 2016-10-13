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

open Sexplib

type grammar_constr_prod_item = Notation_term.grammar_constr_prod_item
val grammar_constr_prod_item_of_sexp : Sexp.t -> grammar_constr_prod_item
val sexp_of_grammar_constr_prod_item : grammar_constr_prod_item -> Sexp.t

type notation_var_internalization_type = Notation_term.notation_var_internalization_type
val notation_var_internalization_type_of_sexp : Sexp.t -> notation_var_internalization_type
val sexp_of_notation_var_internalization_type : notation_var_internalization_type -> Sexp.t

type notation_grammar = Notation_term.notation_grammar
val notation_grammar_of_sexp : Sexp.t -> notation_grammar
val sexp_of_notation_grammar : notation_grammar -> Sexp.t


