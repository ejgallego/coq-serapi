(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_python_runtime_serapi

module Loc        = Ser_loc
module CAst       = Ser_cAst
module Names      = Ser_names
module Constr     = Ser_constr
module UState     = Ser_uState
module Namegen    = Ser_namegen
module Pattern    = Ser_pattern
module Evar_kinds = Ser_evar_kinds
module Genarg     = Ser_genarg
module Libnames   = Ser_libnames
module Glob_term  = Ser_glob_term
module NumTok     = Ser_numTok
module Univ       = Ser_univ

type sort_name_expr =
  [%import: Constrexpr.sort_name_expr]
  [@@deriving sexp,yojson,python]

type univ_level_expr =
  [%import: Constrexpr.univ_level_expr]
  [@@deriving sexp,yojson,python]

type sort_expr =
  [%import: Constrexpr.sort_expr]
  [@@deriving sexp,yojson,python]

type univ_constraint_expr =
  [%import: Constrexpr.univ_constraint_expr]
  [@@deriving sexp,yojson,python]

type instance_expr =
   [%import: Constrexpr.instance_expr]
  [@@deriving sexp,yojson,python]

type 'a or_by_notation_r =
  [%import: 'a Constrexpr.or_by_notation_r]
  [@@deriving sexp,yojson,python]

type 'a or_by_notation =
  [%import: 'a Constrexpr.or_by_notation]
  [@@deriving sexp,yojson,python]

type universe_decl_expr =
  [%import: Constrexpr.universe_decl_expr]
  [@@deriving sexp,yojson,python]

type ident_decl =
  [%import: Constrexpr.ident_decl]
  [@@deriving sexp,yojson,python]

type cumul_univ_decl_expr =
  [%import: Constrexpr.cumul_univ_decl_expr]
  [@@deriving sexp,yojson,python]

type cumul_ident_decl =
  [%import: Constrexpr.cumul_ident_decl]
  [@@deriving sexp,yojson,python]

type name_decl =
  [%import: Constrexpr.name_decl]
  [@@deriving sexp,yojson,python]

type notation_entry =
  [%import: Constrexpr.notation_entry]
  [@@deriving sexp,yojson,python]

type entry_level =
  [%import: Constrexpr.entry_level]
  [@@deriving sexp,yojson,python]

type entry_relative_level =
  [%import: Constrexpr.entry_relative_level]
  [@@deriving sexp,yojson,python]

type notation_entry_level =
  [%import: Constrexpr.notation_entry_level]
  [@@deriving sexp,yojson]

type notation_key =
  [%import: Constrexpr.notation_key]
  [@@deriving sexp,yojson,python]

type notation =  [%import: Constrexpr.notation]
  [@@deriving sexp,yojson,python]

type explicitation = [%import: Constrexpr.explicitation]
  [@@deriving sexp,yojson,python]

type binder_kind = [%import: Constrexpr.binder_kind]
  [@@deriving sexp,yojson,python]

type abstraction_kind = [%import: Constrexpr.abstraction_kind]
  [@@deriving sexp,yojson,python]

type proj_flag = [%import: Constrexpr.proj_flag]
  [@@deriving sexp,yojson,python]

(* type raw_numeral = [%import: Constrexpr.raw_numeral]
 *   [@@deriving sexp,yojson] *)

(* type sign = [%import: Constrexpr.sign]
 *   [@@deriving sexp,yojson] *)

type prim_token = [%import: Constrexpr.prim_token]
  [@@deriving sexp,yojson,python]

type notation_with_optional_scope =
  [%import: Constrexpr.notation_with_optional_scope]
  [@@deriving sexp,yojson,python]

type cases_pattern_expr_r = [%import: Constrexpr.cases_pattern_expr_r]
and cases_pattern_expr = [%import: Constrexpr.cases_pattern_expr]
and kinded_cases_pattern_expr = [%import: Constrexpr.kinded_cases_pattern_expr]
and cases_pattern_notation_substitution = [%import: Constrexpr.cases_pattern_notation_substitution]
and constr_expr_r = [%import: Constrexpr.constr_expr_r]
and constr_expr = [%import: Constrexpr.constr_expr]
and case_expr   = [%import: Constrexpr.case_expr]
and branch_expr = [%import: Constrexpr.branch_expr]
(* and binder_expr = [%import: Constrexpr.binder_expr] *)
and fix_expr    = [%import: Constrexpr.fix_expr]
and cofix_expr  = [%import: Constrexpr.cofix_expr]
and recursion_order_expr_r = [%import: Constrexpr.recursion_order_expr_r]
and recursion_order_expr = [%import: Constrexpr.recursion_order_expr]
and local_binder_expr    = [%import: Constrexpr.local_binder_expr]
and constr_notation_substitution = [%import: Constrexpr.constr_notation_substitution]
  [@@deriving sexp,yojson,python]

type constr_pattern_expr = [%import: Constrexpr.constr_pattern_expr]
  [@@deriving sexp,yojson,python]

type with_declaration_ast =
  [%import: Constrexpr.with_declaration_ast]
  [@@deriving sexp,yojson,python]

type module_ast_r =
  [%import: Constrexpr.module_ast_r]
and module_ast =
  [%import: Constrexpr.module_ast]
  [@@deriving sexp,yojson,python]
