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

type precedence = Ppextend.precedence

val precedence_of_sexp : Sexp.t -> precedence
val sexp_of_precedence : precedence -> Sexp.t

type parenRelation = Ppextend.parenRelation

val parenRelation_of_sexp : Sexp.t -> parenRelation
val sexp_of_parenRelation : parenRelation -> Sexp.t

type tolerability = Ppextend.tolerability

val tolerability_of_sexp : Sexp.t -> tolerability
val sexp_of_tolerability : tolerability -> Sexp.t

type ppbox = Ppextend.ppbox

val ppbox_of_sexp : Sexp.t -> ppbox
val sexp_of_ppbox : ppbox -> Sexp.t

type ppcut = Ppextend.ppcut

val ppcut_of_sexp : Sexp.t -> ppcut
val sexp_of_ppcut : ppcut -> Sexp.t

type unparsing = Ppextend.unparsing

val unparsing_of_sexp : Sexp.t -> unparsing
val sexp_of_unparsing : unparsing -> Sexp.t
