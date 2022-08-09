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

module Level : SerType.SJPHC with type t = Univ.Level.t
module Universe : SerType.SJPHC with type t = Univ.Universe.t

module Variance : SerType.SJPHC with type t = Univ.Variance.t
module Instance : SerType.SJPHC with type t = Univ.Instance.t

type constraint_type = Univ.constraint_type [@@deriving sexp,yojson,python,hash,compare]

type univ_constraint = Univ.univ_constraint

val univ_constraint_of_sexp : Sexp.t -> univ_constraint
val sexp_of_univ_constraint : univ_constraint -> Sexp.t

module Constraints : SerType.SJ with type t = Univ.Constraints.t
module UContext : SerType.S with type t = Univ.UContext.t

module AbstractContext : SerType.SJPHC with type t = Univ.AbstractContext.t

module ContextSet : SerType.SJPHC with type t = Univ.ContextSet.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a Univ.in_universe_context
val in_universe_context_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a in_universe_context
val sexp_of_in_universe_context : ('a -> Sexp.t) -> 'a in_universe_context -> Sexp.t

type 'a in_universe_context_set = 'a Univ.in_universe_context_set
val in_universe_context_set_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a in_universe_context_set
val sexp_of_in_universe_context_set : ('a -> Sexp.t) -> 'a in_universe_context_set -> Sexp.t

type 'a puniverses = 'a * Instance.t
 [@@deriving sexp,yojson,python,hash,compare]

type explanation = Univ.explanation

val explanation_of_sexp : Sexp.t -> explanation
val sexp_of_explanation : explanation -> Sexp.t

