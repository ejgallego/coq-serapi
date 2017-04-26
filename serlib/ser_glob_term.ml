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
module Names      = Ser_names
module Globnames  = Ser_globnames
module Misctypes  = Ser_misctypes
module Decl_kinds = Ser_decl_kinds
module Genarg     = Ser_genarg
module Evar_kinds = Ser_evar_kinds

(**********************************************************************)
(* Glob_term                                                          *)
(**********************************************************************)

type existential_name = Glob_term.existential_name
let existential_name_of_sexp = Names.Id.t_of_sexp
let sexp_of_existential_name = Names.Id.sexp_of_t

type cases_pattern_r = [%import: Glob_term.cases_pattern_r]
and  cases_pattern   = [%import: Glob_term.cases_pattern]
  [@@deriving sexp]

type glob_constr_r = [%import: Glob_term.glob_constr_r]
and glob_constr = [%import: Glob_term.glob_constr]
and glob_decl    = [%import: Glob_term.glob_decl]
and fix_recursion_order = [%import: Glob_term.fix_recursion_order]
and fix_kind            = [%import: Glob_term.fix_kind]
and predicate_pattern   = [%import: Glob_term.predicate_pattern]
and tomatch_tuple  = [%import: Glob_term.tomatch_tuple]
and tomatch_tuples = [%import: Glob_term.tomatch_tuples]
and cases_clause   = [%import: Glob_term.cases_clause]
and cases_clauses  = [%import: Glob_term.cases_clauses]
  [@@deriving sexp]

