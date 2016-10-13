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

type unparsing_rule = Notation.unparsing_rule
val unparsing_rule_of_sexp : Sexp.t -> unparsing_rule
val sexp_of_unparsing_rule : unparsing_rule -> Sexp.t

type extra_unparsing_rules = Notation.extra_unparsing_rules
val extra_unparsing_rules_of_sexp : Sexp.t -> extra_unparsing_rules
val sexp_of_extra_unparsing_rules : extra_unparsing_rules -> Sexp.t

