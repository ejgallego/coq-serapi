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

type 'a or_by_notation = 'a Constrexpr.or_by_notation
val or_by_notation_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a or_by_notation
val sexp_of_or_by_notation : ('a -> Sexp.t) -> 'a or_by_notation -> Sexp.t
val or_by_notation_of_yojson : (Yojson.Safe.t -> ('a, string) Result.result) -> Yojson.Safe.t -> ('a or_by_notation, string) Result.result
val or_by_notation_to_yojson : ('a -> Yojson.Safe.t) -> 'a or_by_notation -> Yojson.Safe.t

type notation_entry = Constrexpr.notation_entry
val notation_entry_of_sexp : Sexp.t -> notation_entry
val sexp_of_notation_entry : notation_entry -> Sexp.t
val notation_entry_of_yojson : Yojson.Safe.t -> (notation_entry, string) Result.result
val notation_entry_to_yojson : notation_entry -> Yojson.Safe.t

type universe_decl_expr = Constrexpr.universe_decl_expr
val universe_decl_expr_of_sexp : Sexp.t -> universe_decl_expr
val sexp_of_universe_decl_expr : universe_decl_expr -> Sexp.t
val universe_decl_expr_of_yojson : Yojson.Safe.t -> (universe_decl_expr, string) Result.result
val universe_decl_expr_to_yojson : universe_decl_expr -> Yojson.Safe.t

type ident_decl = Constrexpr.ident_decl
val ident_decl_of_sexp : Sexp.t -> ident_decl
val sexp_of_ident_decl : ident_decl -> Sexp.t
val ident_decl_of_yojson : Yojson.Safe.t -> (ident_decl, string) Result.result
val ident_decl_to_yojson : ident_decl -> Yojson.Safe.t

type name_decl = Constrexpr.name_decl
val name_decl_of_sexp : Sexp.t -> name_decl
val sexp_of_name_decl : name_decl -> Sexp.t
val name_decl_of_yojson : Yojson.Safe.t -> (name_decl, string) Result.result
val name_decl_to_yojson : name_decl -> Yojson.Safe.t

type notation = Constrexpr.notation

val notation_of_sexp : Sexp.t -> notation
val sexp_of_notation : notation -> Sexp.t

type explicitation = Constrexpr.explicitation

val explicitation_of_sexp : Sexp.t -> explicitation
val sexp_of_explicitation : explicitation -> Sexp.t

type binder_kind = Constrexpr.binder_kind

val binder_kind_of_sexp : Sexp.t -> binder_kind
val sexp_of_binder_kind : binder_kind -> Sexp.t

type abstraction_kind = Constrexpr.abstraction_kind

val abstraction_kind_of_sexp : Sexp.t -> abstraction_kind
val sexp_of_abstraction_kind : abstraction_kind -> Sexp.t

type proj_flag = Constrexpr.proj_flag

val proj_flag_of_sexp : Sexp.t -> proj_flag
val sexp_of_proj_flag : proj_flag -> Sexp.t

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
(* and binder_expr          = Constrexpr.binder_expr *)
and fix_expr             = Constrexpr.fix_expr
and cofix_expr           = Constrexpr.cofix_expr
and recursion_order_expr = Constrexpr.recursion_order_expr
and local_binder_expr    = Constrexpr.local_binder_expr
and constr_notation_substitution = Constrexpr.constr_notation_substitution

val constr_expr_of_sexp : Sexp.t -> constr_expr
val case_expr_of_sexp : Sexp.t -> case_expr
val branch_expr_of_sexp : Sexp.t -> branch_expr
(* val binder_expr_of_sexp : Sexp.t -> binder_expr *)
val fix_expr_of_sexp : Sexp.t -> fix_expr
val cofix_expr_of_sexp : Sexp.t -> cofix_expr
val constr_notation_substitution_of_sexp : Sexp.t -> constr_notation_substitution

val sexp_of_constr_expr : constr_expr -> Sexp.t
val sexp_of_case_expr : case_expr -> Sexp.t
val sexp_of_branch_expr : branch_expr -> Sexp.t
(* val sexp_of_binder_expr : binder_expr -> Sexp.t *)
val sexp_of_fix_expr : fix_expr -> Sexp.t
val sexp_of_cofix_expr : cofix_expr -> Sexp.t
val sexp_of_constr_notation_substitution : constr_notation_substitution -> Sexp.t

val recursion_order_expr_of_sexp : Sexp.t -> recursion_order_expr
val sexp_of_recursion_order_expr : recursion_order_expr -> Sexp.t
val recursion_order_expr_of_yojson : Yojson.Safe.t -> (recursion_order_expr, string) Result.result
val recursion_order_expr_to_yojson : recursion_order_expr -> Yojson.Safe.t

val sexp_of_local_binder_expr : local_binder_expr -> Sexp.t
val local_binder_expr_of_sexp : Sexp.t -> local_binder_expr
val local_binder_expr_of_yojson : Yojson.Safe.t -> (local_binder_expr, string) Result.result
val local_binder_expr_to_yojson : local_binder_expr -> Yojson.Safe.t

val constr_expr_of_yojson : Yojson.Safe.t -> (constr_expr, string) Result.result
val constr_expr_to_yojson : constr_expr -> Yojson.Safe.t

type constr_pattern_expr = Constrexpr.constr_pattern_expr
val constr_pattern_expr_of_sexp : Sexp.t -> constr_pattern_expr
val sexp_of_constr_pattern_expr : constr_pattern_expr -> Sexp.t
val constr_pattern_expr_of_yojson : Yojson.Safe.t -> (constr_pattern_expr, string) Result.result
val constr_pattern_expr_to_yojson : constr_pattern_expr -> Yojson.Safe.t

type with_declaration_ast = Constrexpr.with_declaration_ast

val with_declaration_ast_of_sexp : Sexp.t -> with_declaration_ast
val sexp_of_with_declaration_ast : with_declaration_ast -> Sexp.t
val with_declaration_ast_of_yojson : Yojson.Safe.t -> (with_declaration_ast, string) Result.result
val with_declaration_ast_to_yojson : with_declaration_ast -> Yojson.Safe.t

type module_ast = Constrexpr.module_ast

val module_ast_of_sexp : Sexp.t -> module_ast
val sexp_of_module_ast : module_ast -> Sexp.t
val module_ast_of_yojson : Yojson.Safe.t -> (module_ast, string) Result.result
val module_ast_to_yojson : module_ast -> Yojson.Safe.t
