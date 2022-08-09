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

type 'a or_by_notation = 'a Constrexpr.or_by_notation [@@deriving sexp,yojson,python,hash,compare]
type notation_entry = Constrexpr.notation_entry [@@deriving sexp,yojson,python,hash,compare]

type entry_level = Constrexpr.entry_level
val entry_level_of_sexp : Sexp.t -> entry_level
val sexp_of_entry_level : entry_level -> Sexp.t
val entry_level_of_yojson : Yojson.Safe.t -> (entry_level, string) Result.result
val entry_level_to_yojson : entry_level -> Yojson.Safe.t
val entry_level_of_python : Py.Object.t -> entry_level
val python_of_entry_level : entry_level -> Py.Object.t

type notation_entry_level = Constrexpr.notation_entry_level
val notation_entry_level_of_sexp : Sexp.t -> notation_entry_level
val sexp_of_notation_entry_level : notation_entry_level -> Sexp.t
val notation_entry_level_of_yojson : Yojson.Safe.t -> (notation_entry_level, string) Result.result
val notation_entry_level_to_yojson : notation_entry_level -> Yojson.Safe.t

type entry_relative_level = Constrexpr.entry_relative_level
val entry_relative_level_of_sexp : Sexp.t -> entry_relative_level
val sexp_of_entry_relative_level : entry_relative_level -> Sexp.t
val entry_relative_level_of_yojson : Yojson.Safe.t -> (entry_relative_level, string) Result.result
val entry_relative_level_to_yojson : entry_relative_level -> Yojson.Safe.t
val entry_relative_level_of_python : Py.Object.t -> entry_relative_level
val python_of_entry_relative_level : entry_relative_level -> Py.Object.t

type universe_decl_expr = Constrexpr.universe_decl_expr [@@deriving sexp,yojson,python,hash,compare]
type ident_decl = Constrexpr.ident_decl [@@deriving sexp,yojson,python,hash,compare]
type cumul_ident_decl = Constrexpr.cumul_ident_decl [@@deriving sexp,yojson,python,hash,compare]
type univ_constraint_expr = Constrexpr.univ_constraint_expr [@@deriving sexp,yojson,python,hash,compare]
type name_decl = Constrexpr.name_decl [@@deriving sexp,yojson,python,hash,compare]

type notation = Constrexpr.notation

val notation_of_sexp : Sexp.t -> notation
val sexp_of_notation : notation -> Sexp.t
val notation_of_python : Py.Object.t -> notation
val python_of_notation : notation -> Py.Object.t

type explicitation = Constrexpr.explicitation

val explicitation_of_sexp : Sexp.t -> explicitation
val sexp_of_explicitation : explicitation -> Sexp.t

val explicitation_of_python : Py.Object.t -> explicitation
val python_of_explicitation : explicitation -> Py.Object.t

type binder_kind = Constrexpr.binder_kind

val binder_kind_of_sexp : Sexp.t -> binder_kind
val sexp_of_binder_kind : binder_kind -> Sexp.t

(* type abstraction_kind = Constrexpr.abstraction_kind
 * 
 * val abstraction_kind_of_sexp : Sexp.t -> abstraction_kind
 * val sexp_of_abstraction_kind : abstraction_kind -> Sexp.t *)

(* type proj_flag = Constrexpr.proj_flag
 * 
 * val proj_flag_of_sexp : Sexp.t -> proj_flag
 * val sexp_of_proj_flag : proj_flag -> Sexp.t *)

type prim_token = Constrexpr.prim_token

val prim_token_of_sexp : Sexp.t -> prim_token
val sexp_of_prim_token : prim_token -> Sexp.t

type cases_pattern_expr = Constrexpr.cases_pattern_expr
and cases_pattern_notation_substitution = Constrexpr.cases_pattern_notation_substitution

val cases_pattern_expr_of_sexp : Sexp.t -> cases_pattern_expr
val cases_pattern_notation_substitution_of_sexp : Sexp.t -> cases_pattern_notation_substitution

val sexp_of_cases_pattern_expr : cases_pattern_expr -> Sexp.t
val sexp_of_cases_pattern_notation_substitution : cases_pattern_notation_substitution -> Sexp.t

type instance_expr = Constrexpr.instance_expr

val instance_expr_of_sexp : Sexp.t -> instance_expr
val sexp_of_instance_expr : instance_expr -> Sexp.t

type constr_expr         = Constrexpr.constr_expr
and case_expr            = Constrexpr.case_expr
and branch_expr          = Constrexpr.branch_expr
and fix_expr             = Constrexpr.fix_expr
and cofix_expr           = Constrexpr.cofix_expr
and recursion_order_expr = Constrexpr.recursion_order_expr
and local_binder_expr    = Constrexpr.local_binder_expr
and constr_notation_substitution = Constrexpr.constr_notation_substitution
[@@deriving sexp,yojson,python,hash,compare]

type constr_pattern_expr = Constrexpr.constr_pattern_expr [@@deriving sexp,yojson,python,hash,compare]

type with_declaration_ast = Constrexpr.with_declaration_ast

val with_declaration_ast_of_sexp : Sexp.t -> with_declaration_ast
val sexp_of_with_declaration_ast : with_declaration_ast -> Sexp.t
val with_declaration_ast_of_yojson : Yojson.Safe.t -> (with_declaration_ast, string) Result.result
val with_declaration_ast_to_yojson : with_declaration_ast -> Yojson.Safe.t

type module_ast = Constrexpr.module_ast [@@deriving sexp,yojson,python,hash,compare]
