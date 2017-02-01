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
module Names      = Ser_names
module Bigint     = Ser_bigint
module Misctypes  = Ser_misctypes
module Decl_kinds = Ser_decl_kinds
module Evar_kinds = Ser_evar_kinds
module Genarg     = Ser_genarg
module Libnames   = Ser_libnames
module Glob_term  = Ser_glob_term

type notation =  [%import: Constrexpr.notation]
  [@@deriving sexp]

type explicitation = [%import: Constrexpr.explicitation]
  [@@deriving sexp]

type binder_kind = [%import: Constrexpr.binder_kind]
  [@@deriving sexp]

type abstraction_kind = [%import: Constrexpr.abstraction_kind]
  [@@deriving sexp]

type proj_flag = [%import: Constrexpr.proj_flag]
  [@@deriving sexp]

type prim_token = [%import: Constrexpr.prim_token]
  [@@deriving sexp]

type instance_expr = [%import: Constrexpr.instance_expr]
  [@@deriving sexp]

type cases_pattern_expr = [%import: Constrexpr.cases_pattern_expr]
and cases_pattern_notation_substitution = [%import: Constrexpr.cases_pattern_notation_substitution]
and constr_expr = [%import: Constrexpr.constr_expr]
and case_expr   = [%import: Constrexpr.case_expr]
and branch_expr = [%import: Constrexpr.branch_expr]
and binder_expr = [%import: Constrexpr.binder_expr]
and fix_expr    = [%import: Constrexpr.fix_expr]
and cofix_expr  = [%import: Constrexpr.cofix_expr]
and recursion_order_expr = [%import: Constrexpr.recursion_order_expr]
and local_binder         = [%import: Constrexpr.local_binder]
and constr_notation_substitution = [%import: Constrexpr.constr_notation_substitution]
  [@@deriving sexp]

type constr_pattern_expr = [%import: Constrexpr.constr_pattern_expr]
  [@@deriving sexp]

type typeclass_constraint = [%import: Constrexpr.typeclass_constraint]
and typeclass_context     = [%import: Constrexpr.typeclass_context]
    [@@deriving sexp]

type with_declaration_ast =
  [%import: Constrexpr.with_declaration_ast]
  [@@deriving sexp]

type module_ast =
  [%import: Constrexpr.module_ast]
  [@@deriving sexp]
