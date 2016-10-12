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

module Level : sig

type t = Univ.Level.t
val t_of_sexp : Sexp.t -> t
val sexp_of_t : t -> Sexp.t

end

module Universe : sig

type t = Univ.Universe.t

val t_of_sexp : Sexp.t -> t
val sexp_of_t : t -> Sexp.t

end

type universe = Universe.t

val universe_of_sexp : Sexp.t -> universe
val sexp_of_universe : universe -> Sexp.t

module Instance : sig

type t = Univ.Instance.t
val t_of_sexp : Sexp.t -> t
val sexp_of_t : t -> Sexp.t

end

type constraint_type = Univ.constraint_type

val constraint_type_of_sexp : Sexp.t -> constraint_type
val sexp_of_constraint_type : constraint_type -> Sexp.t

type univ_constraint = Univ.univ_constraint

val univ_constraint_of_sexp : Sexp.t -> univ_constraint
val sexp_of_univ_constraint : univ_constraint -> Sexp.t

type constraints = Univ.constraints

val constraints_of_sexp : Sexp.t -> constraints
val sexp_of_constraints : constraints -> Sexp.t

type universe_instance = Instance.t

val universe_instance_of_sexp : Sexp.t -> universe_instance
val sexp_of_universe_instance : universe_instance -> Sexp.t

type 'a puniverses = 'a * universe_instance

val puniverses_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a puniverses
val sexp_of_puniverses : ('a -> Sexp.t) -> 'a puniverses -> Sexp.t

type explanation = Univ.explanation

val explanation_of_sexp : Sexp.t -> explanation
val sexp_of_explanation : explanation -> Sexp.t

type univ_inconsistency = Univ.univ_inconsistency

val univ_inconsistency_of_sexp : Sexp.t -> univ_inconsistency
val sexp_of_univ_inconsistency : univ_inconsistency -> Sexp.t

