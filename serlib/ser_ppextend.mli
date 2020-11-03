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

type ppbox = Ppextend.ppbox

val ppbox_of_sexp : Sexp.t -> ppbox
val sexp_of_ppbox : ppbox -> Sexp.t

type ppcut = Ppextend.ppcut

val ppcut_of_sexp : Sexp.t -> ppcut
val sexp_of_ppcut : ppcut -> Sexp.t

type unparsing_rule = Ppextend.unparsing_rule
val unparsing_rule_of_sexp : Sexp.t -> unparsing_rule
val sexp_of_unparsing_rule : unparsing_rule -> Sexp.t
val unparsing_rule_of_python : Py.Object.t -> unparsing_rule
val python_of_unparsing_rule : unparsing_rule -> Py.Object.t

type extra_unparsing_rules = Ppextend.extra_unparsing_rules
  [@@deriving sexp,python]

type notation_printing_rules = Ppextend.notation_printing_rules
  [@@deriving sexp,python]
