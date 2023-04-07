(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type infix_flag =
  [%import: Vernacexpr.infix_flag]
  [@@deriving sexp,yojson]

type scope_name =
  [%import: Vernacexpr.scope_name]
  [@@deriving sexp,yojson]

type notation_format =
  [%import: Vernacexpr.notation_format]
  [@@deriving sexp,yojson]

type syntax_modifier =
  [%import: Vernacexpr.syntax_modifier]
  [@@deriving sexp,yojson]

type coercion_class = Vernacexpr.coercion_class
val coercion_class_of_sexp : Sexp.t -> coercion_class
val sexp_of_coercion_class : coercion_class -> Sexp.t

(* type goal_identifier = Vernacexpr.goal_identifier
 * val goal_identifier_of_sexp : Sexp.t -> goal_identifier
 * val sexp_of_goal_identifier : goal_identifier -> Sexp.t *)

type goal_reference = Vernacexpr.goal_reference
val goal_reference_of_sexp : Sexp.t -> goal_reference
val sexp_of_goal_reference : goal_reference -> Sexp.t

type printable = Vernacexpr.printable
val printable_of_sexp : Sexp.t -> printable
val sexp_of_printable : printable -> Sexp.t

type search_item = Vernacexpr.search_item
val search_item_of_sexp : Sexp.t -> search_item
val sexp_of_search_item : search_item -> Sexp.t

type searchable = Vernacexpr.searchable
val searchable_of_sexp : Sexp.t -> searchable
val sexp_of_searchable : searchable -> Sexp.t

type locatable = Vernacexpr.locatable
val locatable_of_sexp : Sexp.t -> locatable
val sexp_of_locatable : locatable -> Sexp.t

type showable = Vernacexpr.showable
val showable_of_sexp : Sexp.t -> showable
val sexp_of_showable : showable -> Sexp.t

type comment = Vernacexpr.comment
val comment_of_sexp : Sexp.t -> comment
val sexp_of_comment : comment -> Sexp.t

type search_restriction = Vernacexpr.search_restriction
val search_restriction_of_sexp : Sexp.t -> search_restriction
val sexp_of_search_restriction : search_restriction -> Sexp.t

(* type rec_flag = Vernacexpr.rec_flag
 * val rec_flag_of_sexp : Sexp.t -> rec_flag
 * val sexp_of_rec_flag : rec_flag -> Sexp.t *)

type verbose_flag = Vernacexpr.verbose_flag
val verbose_flag_of_sexp : Sexp.t -> verbose_flag
val sexp_of_verbose_flag : verbose_flag -> Sexp.t

type coercion_flag = Vernacexpr.coercion_flag
val coercion_flag_of_sexp : Sexp.t -> coercion_flag
val sexp_of_coercion_flag : coercion_flag -> Sexp.t

(* type inductive_flag = Vernacexpr.inductive_flag
 * val inductive_flag_of_sexp : Sexp.t -> inductive_flag
 * val sexp_of_inductive_flag : inductive_flag -> Sexp.t *)

type instance_flag = Vernacexpr.instance_flag
val instance_flag_of_sexp : Sexp.t -> instance_flag
val sexp_of_instance_flag : instance_flag -> Sexp.t

type export_flag = Vernacexpr.export_flag
val export_flag_of_sexp : Sexp.t -> export_flag
val sexp_of_export_flag : export_flag -> Sexp.t

(* type onlyparsing_flag = Vernacexpr.onlyparsing_flag
 * val onlyparsing_flag_of_sexp : Sexp.t -> onlyparsing_flag
 * val sexp_of_onlyparsing_flag : onlyparsing_flag -> Sexp.t *)

type locality_flag = Vernacexpr.locality_flag
val locality_flag_of_sexp : Sexp.t -> locality_flag
val sexp_of_locality_flag : locality_flag -> Sexp.t

(* type obsolete_locality = Vernacexpr.obsolete_locality
 * val obsolete_locality_of_sexp : Sexp.t -> obsolete_locality
 * val sexp_of_obsolete_locality : obsolete_locality -> Sexp.t *)

(* type option_value = Vernacexpr.option_value
 * val option_value_of_sexp : Sexp.t -> option_value
 * val sexp_of_option_value : option_value -> Sexp.t *)

(* type option_ref_value = Vernacexpr.option_ref_value
 * val option_ref_value_of_sexp : Sexp.t -> option_ref_value
 * val sexp_of_option_ref_value : option_ref_value -> Sexp.t *)

(* type plident = Vernacexpr.plident
 * val plident_of_sexp : Sexp.t -> plident
 * val sexp_of_plident : plident -> Sexp.t *)

(* type sort_expr = Vernacexpr.sort_expr
 * val sort_expr_of_sexp : Sexp.t -> sort_expr
 * val sexp_of_sort_expr : sort_expr -> Sexp.t *)

type definition_expr = Vernacexpr.definition_expr
val definition_expr_of_sexp : Sexp.t -> definition_expr
val sexp_of_definition_expr : definition_expr -> Sexp.t

type fixpoint_expr = Vernacexpr.fixpoint_expr
  [@@deriving sexp,hash,compare]

type cofixpoint_expr = Vernacexpr.cofixpoint_expr
val cofixpoint_expr_of_sexp : Sexp.t -> cofixpoint_expr
val sexp_of_cofixpoint_expr : cofixpoint_expr -> Sexp.t

type local_decl_expr = Vernacexpr.local_decl_expr
val local_decl_expr_of_sexp : Sexp.t -> local_decl_expr
val sexp_of_local_decl_expr : local_decl_expr -> Sexp.t

type inductive_kind = Vernacexpr.inductive_kind
val inductive_kind_of_sexp : Sexp.t -> inductive_kind
val sexp_of_inductive_kind : inductive_kind -> Sexp.t

type notation_declaration = Vernacexpr.notation_declaration
val notation_declaration_of_sexp : Sexp.t -> notation_declaration
val sexp_of_notation_declaration : notation_declaration -> Sexp.t

type simple_binder = Vernacexpr.simple_binder
val simple_binder_of_sexp : Sexp.t -> simple_binder
val sexp_of_simple_binder : simple_binder -> Sexp.t

type class_binder = Vernacexpr.class_binder

val class_binder_of_sexp : Sexp.t -> class_binder
val sexp_of_class_binder : class_binder -> Sexp.t

type 'a with_coercion = 'a Vernacexpr.with_coercion

val with_coercion_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a with_coercion
val sexp_of_with_coercion : ('a -> Sexp.t) -> 'a with_coercion -> Sexp.t

type constructor_expr = Vernacexpr.constructor_expr
val constructor_expr_of_sexp : Sexp.t -> constructor_expr
val sexp_of_constructor_expr : constructor_expr -> Sexp.t

type constructor_list_or_record_decl_expr = Vernacexpr.constructor_list_or_record_decl_expr

val constructor_list_or_record_decl_expr_of_sexp :
  Sexp.t -> constructor_list_or_record_decl_expr
val sexp_of_constructor_list_or_record_decl_expr :
  constructor_list_or_record_decl_expr -> Sexp.t

type inductive_expr = Vernacexpr.inductive_expr

val inductive_expr_of_sexp : Sexp.t -> inductive_expr
val sexp_of_inductive_expr : inductive_expr -> Sexp.t

type one_inductive_expr = Vernacexpr.one_inductive_expr

val one_inductive_expr_of_sexp : Sexp.t -> one_inductive_expr
val sexp_of_one_inductive_expr : one_inductive_expr -> Sexp.t

type proof_expr = Vernacexpr.proof_expr

val proof_expr_of_sexp : Sexp.t -> proof_expr
val sexp_of_proof_expr : proof_expr -> Sexp.t

(* type grammar_tactic_prod_item_expr = Vernacexpr.grammar_tactic_prod_item_expr *)
(* val grammar_tactic_prod_item_expr_of_sexp : Sexp.t -> grammar_tactic_prod_item_expr *)
(* val sexp_of_grammar_tactic_prod_item_expr : grammar_tactic_prod_item_expr -> Sexp.t *)

(* type syntax_modifier = Vernacexpr.syntax_modifier *)

(* val syntax_modifier_of_sexp : Sexp.t -> syntax_modifier *)
(* val sexp_of_syntax_modifier : syntax_modifier -> Sexp.t *)

type proof_end = Vernacexpr.proof_end
val proof_end_of_sexp : Sexp.t -> proof_end
val sexp_of_proof_end : proof_end -> Sexp.t

type scheme = Vernacexpr.scheme
val scheme_of_sexp : Sexp.t -> scheme
val sexp_of_scheme : scheme -> Sexp.t

type section_subset_expr = Vernacexpr.section_subset_expr
val section_subset_expr_of_sexp : Sexp.t -> section_subset_expr
val sexp_of_section_subset_expr : section_subset_expr -> Sexp.t

type extend_name = Vernacexpr.extend_name
val extend_name_of_sexp : Sexp.t -> extend_name
val sexp_of_extend_name : extend_name -> Sexp.t

type register_kind = Vernacexpr.register_kind
val register_kind_of_sexp : Sexp.t -> register_kind
val sexp_of_register_kind : register_kind -> Sexp.t

type module_ast_inl = Vernacexpr.module_ast_inl

val module_ast_inl_of_sexp : Sexp.t -> module_ast_inl
val sexp_of_module_ast_inl : module_ast_inl -> Sexp.t

type module_binder = Vernacexpr.module_binder

val module_binder_of_sexp : Sexp.t -> module_binder
val sexp_of_module_binder : module_binder -> Sexp.t

type discharge =
  [%import: Vernacexpr.discharge]
  [@@deriving sexp,yojson]

type equality_scheme_type =
  [%import: Vernacexpr.equality_scheme_type]
  [@@deriving sexp,yojson]

type import_categories =
  [%import: Vernacexpr.import_categories]
  [@@deriving sexp,yojson]

type export_with_cats =
  [%import: Vernacexpr.export_with_cats]
  [@@deriving sexp,yojson]

type one_import_filter_name =
  [%import: Vernacexpr.one_import_filter_name]
  [@@deriving sexp,yojson]

type import_filter_expr =
  [%import: Vernacexpr.import_filter_expr]
  [@@deriving sexp,yojson]

type hint_info_expr =
  [%import: Vernacexpr.hint_info_expr]
  [@@deriving sexp,yojson]

type reference_or_constr =
  [%import: Vernacexpr.reference_or_constr]
  [@@deriving sexp,yojson]

type hints_expr =
  [%import: Vernacexpr.hints_expr]
  [@@deriving sexp,yojson]

type vernac_one_argument_status =
  [%import: Vernacexpr.vernac_one_argument_status]
  [@@deriving sexp,yojson]

type vernac_argument_status =
  [%import: Vernacexpr.vernac_argument_status]
  [@@deriving sexp,yojson]

type arguments_modifier =
  [%import: Vernacexpr.arguments_modifier]
  [@@deriving sexp,yojson]

type option_setting =
  [%import: Vernacexpr.option_setting]
  [@@deriving sexp,yojson]

type notation_enable_modifier =
  [%import: Vernacexpr.notation_enable_modifier]
  [@@deriving sexp, yojson]

type synterp_vernac_expr =
  [%import: Vernacexpr.synterp_vernac_expr]
  [@@deriving sexp,yojson]

type synpure_vernac_expr =
  [%import: Vernacexpr.synpure_vernac_expr]
  [@@deriving sexp,yojson]

type 'a vernac_expr_gen =
  [%import: 'a Vernacexpr.vernac_expr_gen]
  [@@deriving sexp, yojson]

type control_flag =
  [%import: Vernacexpr.control_flag]
  [@@deriving sexp, yojson]

type ('a, 'b) vernac_control_gen_r =
  [%import: ('a, 'b) Vernacexpr.vernac_control_gen_r]
  [@@deriving sexp,yojson]

type 'a vernac_control_gen =
  [%import: 'a Vernacexpr.vernac_control_gen]
  [@@deriving sexp,yojson]

type vernac_control =
  [%import: Vernacexpr.vernac_control]
  [@@deriving sexp,yojson,hash,compare]
