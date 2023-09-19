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

module Level : SerType.SJHC with type t = Univ.Level.t
module Universe : SerType.SJHC with type t = Univ.Universe.t

type constraint_type = Univ.constraint_type [@@deriving sexp,yojson,hash,compare]

type univ_constraint = Univ.univ_constraint

val univ_constraint_of_sexp : Sexp.t -> univ_constraint
val sexp_of_univ_constraint : univ_constraint -> Sexp.t

module Constraints : SerType.SJHC with type t = Univ.Constraints.t

module ContextSet : SerType.SJHC with type t = Univ.ContextSet.t

type 'a in_universe_context_set = 'a Univ.in_universe_context_set
val in_universe_context_set_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a in_universe_context_set
val sexp_of_in_universe_context_set : ('a -> Sexp.t) -> 'a in_universe_context_set -> Sexp.t
