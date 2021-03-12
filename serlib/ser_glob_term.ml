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

module Loc        = Ser_loc
module CAst       = Ser_cAst
module DAst       = Ser_dAst
module Names      = Ser_names
module Univ       = Ser_univ
module Uint63     = Ser_uint63
module Float64    = Ser_float64
module Constr     = Ser_constr
module Libnames   = Ser_libnames
module Genarg     = Ser_genarg
module Evar_kinds = Ser_evar_kinds
module Namegen    = Ser_namegen

(**********************************************************************)
(* Glob_term                                                          *)
(**********************************************************************)

type binding_kind =
  [%import: Glob_term.binding_kind]
  [@@deriving sexp,yojson]

(* type 'a universe_kind =
 *   [%import: 'a Glob_term.universe_kind]
 *   [@@deriving sexp,yojson] *)

(* type level_info =
 *   [%import: Glob_term.level_info]
 *   [@@deriving sexp,yojson] *)

type glob_sort_name =
  [%import: Glob_term.glob_sort_name]
  [@@deriving sexp,yojson]

type 'a glob_sort_gen =
  [%import: 'a Glob_term.glob_sort_gen]
  [@@deriving sexp,yojson]

(* type 'a glob_sort_expr =
 *   [%import: 'a Glob_term.glob_sort_expr]
 *   [@@deriving sexp,yojson] *)

type glob_level =
  [%import: Glob_term.glob_level]
  [@@deriving sexp,yojson]

type glob_constraint =
  [%import: Glob_term.glob_constraint]
  [@@deriving sexp,yojson]

(* type sort_info =
 *   [%import: Glob_term.sort_info]
 *   [@@deriving sexp,yojson] *)

type glob_sort =
  [%import: Glob_term.glob_sort]
  [@@deriving sexp,yojson]

type 'a cast_type =
  [%import: 'a Glob_term.cast_type]
  [@@deriving sexp,yojson]

type existential_name =
  [%import: Glob_term.existential_name]
  [@@deriving sexp,yojson]

type 'a cases_pattern_r = [%import: 'a Glob_term.cases_pattern_r]
and 'a cases_pattern_g  = [%import: 'a Glob_term.cases_pattern_g]
  [@@deriving sexp]

type cases_pattern =
  [%import: Glob_term.cases_pattern]
  [@@deriving sexp]

type glob_recarg =
  [%import: Glob_term.glob_recarg]
  [@@deriving sexp]

type glob_fix_kind =
  [%import: Glob_term.glob_fix_kind]
  [@@deriving sexp]

type 'a glob_constr_r        = [%import: 'a Glob_term.glob_constr_r]
and 'a glob_constr_g         = [%import: 'a Glob_term.glob_constr_g]
and 'a glob_decl_g           = [%import: 'a Glob_term.glob_decl_g]
and 'a predicate_pattern_g   = [%import: 'a Glob_term.predicate_pattern_g]
and 'a tomatch_tuple_g       = [%import: 'a Glob_term.tomatch_tuple_g]
and 'a tomatch_tuples_g      = [%import: 'a Glob_term.tomatch_tuples_g]
and 'a cases_clause_g        = [%import: 'a Glob_term.cases_clause_g]
and 'a cases_clauses_g       = [%import: 'a Glob_term.cases_clauses_g]
  [@@deriving sexp]

type glob_constr =
  [%import: Glob_term.glob_constr]
  [@@deriving sexp]

type glob_decl =
  [%import: Glob_term.glob_decl]
  [@@deriving sexp]

type predicate_pattern   = [%import: Glob_term.predicate_pattern]
  [@@deriving sexp]

type tomatch_tuple       = [%import: Glob_term.tomatch_tuple]
  [@@deriving sexp]

type tomatch_tuples      = [%import: Glob_term.tomatch_tuples]
  [@@deriving sexp]

type cases_clause        = [%import: Glob_term.cases_clause]
  [@@deriving sexp]

type cases_clauses       = [%import: Glob_term.cases_clauses]
  [@@deriving sexp]

