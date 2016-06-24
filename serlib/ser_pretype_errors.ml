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

open Ser_constr
open Ser_evd
open Ser_evar
open Ser_environ
open Ser_names
open Ser_univ
open Ser_type_errors

open Ser_locus
open Ser_evar_kinds

type unification_error =
  [%import: Pretype_errors.unification_error
  [@with
    Univ.univ_inconsistency := univ_inconsistency;
    Evd.evar_constraint := evar_constraint;
    Environ.env := env;
    Term.constr := constr;
    Term.types  := constr;
    Term.existential_key := existential_key;
    Term.existential     := existential;
  ]]
  [@@deriving sexp]

type position =
  [%import: Pretype_errors.position
  [@with
    Names.Id.t := id;
    Locus.hyp_location_flag := hyp_location_flag;
    Term.constr := constr;
    Term.types  := constr;
  ]]
  [@@deriving sexp]

type position_reporting =
  [%import: Pretype_errors.position_reporting
  [@with
    Term.constr := constr;
  ]]
  [@@deriving sexp]

type subterm_unification_error =
  [%import: Pretype_errors.subterm_unification_error
  [@with
    Term.constr := constr;
  ]]
  [@@deriving sexp]

type pretype_error =
  [%import: Pretype_errors.pretype_error
  [@with
    Names.Id.t := id;
    Names.Name.t := name;
    Term.constr := constr;
    Term.types  := constr;
    Term.existential_key := existential_key;
    Environ.unsafe_judgment := unsafe_judgment;
    Environ.env := env;
    Evd.unsolvability_explanation := unsolvability_explanation;
    Type_errors.type_error := type_error;
    Evar_kinds.t := evar_kinds;
    Evar.Set.t   := evar_set;
  ]]
  [@@deriving sexp]
