(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv

module Loc         = Ser_loc
module CAst        = Ser_cAst
module Names       = Ser_names
module Flags       = Ser_flags
module Sorts       = Ser_sorts
module CPrimitives = Ser_cPrimitives
module Univ        = Ser_univ
module UnivNames   = Ser_univNames
module Conv_oracle = Ser_conv_oracle
module Declarations= Ser_declarations
module Decls       = Ser_decls
module Genarg      = Ser_genarg
module Declaremods = Ser_declaremods
module Libnames    = Ser_libnames
module Extend      = Ser_extend
module Stateid     = Ser_stateid
module Glob_term     = Ser_glob_term
module Goal_select   = Ser_goal_select
module Proof_global  = Ser_proof_global
module Proof_bullet  = Ser_proof_bullet
module Constrexpr    = Ser_constrexpr
module Notation_term = Ser_notation_term
module Hints         = Ser_hints
module Goptions      = Ser_goptions
module Genredexpr    = Ser_genredexpr
module Universes     = Ser_universes
module Attributes    = Ser_attributes
module Gramlib       = Ser_gramlib
module Impargs       = Ser_impargs

type class_rawexpr = [%import: Vernacexpr.class_rawexpr]
  [@@deriving sexp,yojson]

type goal_identifier = [%import: Vernacexpr.goal_identifier]
  [@@deriving sexp]

type scope_name      = [%import: Vernacexpr.scope_name]
  [@@deriving sexp,yojson]

type goal_reference =
  [%import: Vernacexpr.goal_reference]
  [@@deriving sexp,yojson]

type printable =
  [%import: Vernacexpr.printable]
  [@@deriving sexp,yojson]

type vernac_cumulative =
  [%import: Vernacexpr.vernac_cumulative]
  [@@deriving sexp,yojson]

type search_about_item =
  [%import: Vernacexpr.search_about_item]
  [@@deriving sexp,yojson]

type searchable =
  [%import: Vernacexpr.searchable]
  [@@deriving sexp,yojson]

type locatable = [%import: Vernacexpr.locatable]
  [@@deriving sexp,yojson]

type showable =  [%import: Vernacexpr.showable]
  [@@deriving sexp,yojson]

type comment =
  [%import: Vernacexpr.comment]
  [@@deriving sexp,yojson]

type search_restriction =  [%import: Vernacexpr.search_restriction]
  [@@deriving sexp,yojson]

type rec_flag          = [%import: Vernacexpr.rec_flag          ] [@@deriving sexp,yojson]
type verbose_flag      = [%import: Vernacexpr.verbose_flag      ] [@@deriving sexp,yojson]
type coercion_flag     = [%import: Vernacexpr.coercion_flag     ] [@@deriving sexp,yojson]
type inductive_flag    = [%import: Vernacexpr.inductive_flag    ] [@@deriving sexp,yojson]
type instance_flag     = [%import: Vernacexpr.instance_flag     ] [@@deriving sexp,yojson]
type export_flag       = [%import: Vernacexpr.export_flag       ] [@@deriving sexp,yojson]
type onlyparsing_flag  = [%import: Vernacexpr.onlyparsing_flag  ] [@@deriving sexp,yojson]
type locality_flag     = [%import: Vernacexpr.locality_flag     ] [@@deriving sexp,yojson]
(* type obsolete_locality = [%import: Vernacexpr.obsolete_locality ] [@@deriving sexp] *)

type option_setting =
  [%import: Vernacexpr.option_setting]
  [@@deriving sexp,yojson]

type option_ref_value =
  [%import: Vernacexpr.option_ref_value]
  [@@deriving sexp,yojson]

(* type plident =
 *   [%import: Vernacexpr.plident ]
 *   [@@deriving sexp] *)

type sort_expr =
  [%import: Vernacexpr.sort_expr]
  [@@deriving sexp,yojson]

type definition_expr =
  [%import: Vernacexpr.definition_expr]
  [@@deriving sexp,yojson]

type decl_notation =
  [%import: Vernacexpr.decl_notation]
  [@@deriving sexp,yojson]

type 'a fix_expr_gen =
  [%import: 'a Vernacexpr.fix_expr_gen]
  [@@deriving sexp,yojson]

type fixpoint_expr =
  [%import: Vernacexpr.fixpoint_expr]
  [@@deriving sexp,yojson]

type cofixpoint_expr =
  [%import: Vernacexpr.cofixpoint_expr]
  [@@deriving sexp,yojson]

type local_decl_expr =
  [%import: Vernacexpr.local_decl_expr]
  [@@deriving sexp,yojson]

type inductive_kind =
  [%import: Vernacexpr.inductive_kind]
  [@@deriving sexp,yojson]

type simple_binder =
  [%import: Vernacexpr.simple_binder]
  [@@deriving sexp,yojson]

type class_binder =
  [%import: Vernacexpr.class_binder]
  [@@deriving sexp,yojson]

type 'a with_coercion =
  [%import: 'a Vernacexpr.with_coercion]
  [@@deriving sexp,yojson]

(* type 'a with_instance =
 *   [%import: 'a Vernacexpr.with_instance]
 *   [@@deriving sexp,yojson] *)

(* type 'a with_notation =
 *   [%import: 'a Vernacexpr.with_notation]
 *   [@@deriving sexp,yojson] *)

(* type 'a with_priority =
 *   [%import: 'a Vernacexpr.with_priority]
 *   [@@deriving sexp,yojson] *)

type constructor_expr =
  [%import: Vernacexpr.constructor_expr]
  [@@deriving sexp,yojson]

type record_field_attr =
  [%import: Vernacexpr.record_field_attr]
  [@@deriving sexp,yojson]

type constructor_list_or_record_decl_expr =
  [%import: Vernacexpr.constructor_list_or_record_decl_expr]
  [@@deriving sexp,yojson]

type inductive_expr =
  [%import: Vernacexpr.inductive_expr]
  [@@deriving sexp,yojson]

type one_inductive_expr =
  [%import: Vernacexpr.one_inductive_expr]
  [@@deriving sexp,yojson]

type proof_expr =
  [%import: Vernacexpr.proof_expr]
  [@@deriving sexp,yojson]

type syntax_modifier =
  [%import: Vernacexpr.syntax_modifier]
  [@@deriving sexp,yojson]

type proof_end =
  [%import: Vernacexpr.proof_end]
  [@@deriving sexp,yojson]

type scheme =
  [%import: Vernacexpr.scheme]
  [@@deriving sexp,yojson]

type section_subset_expr =
  [%import: Vernacexpr.section_subset_expr]
  [@@deriving sexp,yojson]

type extend_name =
  [%import: Vernacexpr.extend_name]
  [@@deriving sexp,yojson]

type register_kind =
  [%import: Vernacexpr.register_kind]
  [@@deriving sexp,yojson]

type module_ast_inl =
  [%import: Vernacexpr.module_ast_inl]
  [@@deriving sexp,yojson]

type module_binder =
  [%import: Vernacexpr.module_binder]
  [@@deriving sexp,yojson]

type typeclass_constraint =
  [%import: Vernacexpr.typeclass_constraint]
  [@@deriving sexp,yojson]

type discharge =
  [%import: Vernacexpr.discharge]
  [@@deriving sexp,yojson]

type arguments_modifier =
  [%import: Vernacexpr.arguments_modifier]
  [@@deriving sexp,yojson]

type vernac_one_argument_status =
  [%import: Vernacexpr.vernac_one_argument_status]
  [@@deriving sexp,yojson]

type vernac_argument_status =
  [%import: Vernacexpr.vernac_argument_status]
  [@@deriving sexp,yojson]

type vernac_expr =
  [%import: Vernacexpr.vernac_expr]
  [@@deriving sexp, yojson]

type control_flag =
  [%import: Vernacexpr.control_flag]
  [@@deriving sexp, yojson]

type vernac_control_r =
  [%import: Vernacexpr.vernac_control_r]
  [@@deriving sexp, yojson]

type vernac_control =
  [%import: Vernacexpr.vernac_control]
  [@@deriving sexp, yojson]
