(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2020 MINES ParisTech / Inria                          *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv
open Ppx_python_runtime_serapi

module CUnix       = Ser_cUnix
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
module Typeclasses   = Ser_typeclasses

type class_rawexpr = [%import: Vernacexpr.class_rawexpr]
  [@@deriving sexp,yojson,python]

type goal_identifier = [%import: Vernacexpr.goal_identifier]
  [@@deriving sexp]

type scope_name      = [%import: Vernacexpr.scope_name]
  [@@deriving sexp,yojson,python]

type goal_reference =
  [%import: Vernacexpr.goal_reference]
  [@@deriving sexp,yojson,python]

type printable =
  [%import: Vernacexpr.printable]
  [@@deriving sexp,yojson,python]

(* type vernac_cumulative =
 *   [%import: Vernacexpr.vernac_cumulative]
 *   [@@deriving sexp,yojson,python] *)

type glob_search_where =
  [%import: Vernacexpr.glob_search_where]
  [@@deriving sexp,yojson,python]

type search_item =
  [%import: Vernacexpr.search_item]
  [@@deriving sexp,yojson,python]

type search_request =
  [%import: Vernacexpr.search_request]
  [@@deriving sexp,yojson,python]

type searchable =
  [%import: Vernacexpr.searchable]
  [@@deriving sexp,yojson,python]

type locatable = [%import: Vernacexpr.locatable]
  [@@deriving sexp,yojson,python]

type showable =  [%import: Vernacexpr.showable]
  [@@deriving sexp,yojson,python]

type comment =
  [%import: Vernacexpr.comment]
  [@@deriving sexp,yojson,python]

type search_restriction =  [%import: Vernacexpr.search_restriction]
  [@@deriving sexp,yojson,python]

(* type rec_flag          = [%import: Vernacexpr.rec_flag          ] [@@deriving sexp,yojson] *)
type verbose_flag      = [%import: Vernacexpr.verbose_flag      ] [@@deriving sexp,yojson,python]
type coercion_flag     = [%import: Vernacexpr.coercion_flag     ] [@@deriving sexp,yojson,python]
(* type inductive_flag    = [%import: Vernacexpr.inductive_flag    ] [@@deriving sexp,yojson] *)
type instance_flag     = [%import: Vernacexpr.instance_flag     ] [@@deriving sexp,yojson,python]
type export_flag       = [%import: Vernacexpr.export_flag       ] [@@deriving sexp,yojson,python]
(* type onlyparsing_flag  = [%import: Vernacexpr.onlyparsing_flag  ] [@@deriving sexp,yojson] *)
type locality_flag     = [%import: Vernacexpr.locality_flag     ] [@@deriving sexp,yojson,python]
(* type obsolete_locality = [%import: Vernacexpr.obsolete_locality ] [@@deriving sexp] *)

type option_setting =
  [%import: Vernacexpr.option_setting]
  [@@deriving sexp,yojson,python]

(* type option_ref_value =
 *   [%import: Vernacexpr.option_ref_value]
 *   [@@deriving sexp,yojson,python] *)

(* type plident =
 *   [%import: Vernacexpr.plident ]
 *   [@@deriving sexp] *)

(* type sort_expr =
 *   [%import: Vernacexpr.sort_expr]
 *   [@@deriving sexp,yojson] *)

type definition_expr =
  [%import: Vernacexpr.definition_expr]
  [@@deriving sexp,yojson,python]

type syntax_modifier =
  [%import: Vernacexpr.syntax_modifier]
  [@@deriving sexp,yojson,python]

type decl_notation =
  [%import: Vernacexpr.decl_notation]
  [@@deriving sexp,yojson,python]

type 'a fix_expr_gen =
  [%import: 'a Vernacexpr.fix_expr_gen]
  [@@deriving sexp,yojson,python]

type fixpoint_expr =
  [%import: Vernacexpr.fixpoint_expr]
  [@@deriving sexp,yojson,python]

type cofixpoint_expr =
  [%import: Vernacexpr.cofixpoint_expr]
  [@@deriving sexp,yojson,python]

type local_decl_expr =
  [%import: Vernacexpr.local_decl_expr]
  [@@deriving sexp,yojson,python]

type inductive_kind =
  [%import: Vernacexpr.inductive_kind]
  [@@deriving sexp,yojson,python]

type simple_binder =
  [%import: Vernacexpr.simple_binder]
  [@@deriving sexp,yojson,python]

type class_binder =
  [%import: Vernacexpr.class_binder]
  [@@deriving sexp,yojson,python]

type 'a with_coercion =
  [%import: 'a Vernacexpr.with_coercion]
  [@@deriving sexp,yojson,python]

(* type 'a with_instance =
 *   [%import: 'a Vernacexpr.with_instance]
 *   [@@deriving sexp,yojson,python] *)

(* type 'a with_notation =
 *   [%import: 'a Vernacexpr.with_notation]
 *   [@@deriving sexp,yojson,python] *)

(* type 'a with_priority =
 *   [%import: 'a Vernacexpr.with_priority]
 *   [@@deriving sexp,yojson,python] *)

type constructor_expr =
  [%import: Vernacexpr.constructor_expr]
  [@@deriving sexp,yojson,python]

type record_field_attr =
  [%import: Vernacexpr.record_field_attr]
  [@@deriving sexp,yojson,python]

type constructor_list_or_record_decl_expr =
  [%import: Vernacexpr.constructor_list_or_record_decl_expr]
  [@@deriving sexp,yojson,python]

type inductive_params_expr =
  [%import: Vernacexpr.inductive_params_expr]
  [@@deriving sexp,yojson,python]

type inductive_expr =
  [%import: Vernacexpr.inductive_expr]
  [@@deriving sexp,yojson,python]

type one_inductive_expr =
  [%import: Vernacexpr.one_inductive_expr]
  [@@deriving sexp,yojson,python]

type proof_expr =
  [%import: Vernacexpr.proof_expr]
  [@@deriving sexp,yojson,python]

type opacity_flag =
  [%import: Vernacexpr.opacity_flag]
  [@@deriving sexp,yojson,python]

type proof_end =
  [%import: Vernacexpr.proof_end]
  [@@deriving sexp,yojson,python]

type one_import_filter_name =
  [%import: Vernacexpr.one_import_filter_name]
  [@@deriving sexp,yojson,python]

type import_filter_expr =
  [%import: Vernacexpr.import_filter_expr]
  [@@deriving sexp,yojson,python]

type scheme =
  [%import: Vernacexpr.scheme]
  [@@deriving sexp,yojson,python]

type section_subset_expr =
  [%import: Vernacexpr.section_subset_expr]
  [@@deriving sexp,yojson,python]

type extend_name =
  [%import: Vernacexpr.extend_name]
  [@@deriving sexp,yojson,python]

type register_kind =
  [%import: Vernacexpr.register_kind]
  [@@deriving sexp,yojson,python]

type module_ast_inl =
  [%import: Vernacexpr.module_ast_inl]
  [@@deriving sexp,yojson,python]

type module_binder =
  [%import: Vernacexpr.module_binder]
  [@@deriving sexp,yojson,python]

type typeclass_constraint =
  [%import: Vernacexpr.typeclass_constraint]
  [@@deriving sexp,yojson,python]

type discharge =
  [%import: Vernacexpr.discharge]
  [@@deriving sexp,yojson,python]

module AM = struct
  type _t =
    | Assert
    | ClearBidiHint
    | ClearImplicits
    | ClearScopes
    | DefaultImplicits
    | ExtraScopes
    | ReductionDontExposeCase
    | ReductionNeverUnfold
    | Rename
  [@@deriving python]

  type t = Vernacexpr.arguments_modifier

  let _to (x : t) : _t = match x with
    | `Assert -> Assert
    | `ClearBidiHint -> ClearBidiHint
    | `ClearImplicits -> ClearImplicits
    | `ClearScopes -> ClearScopes
    | `DefaultImplicits -> DefaultImplicits
    | `ExtraScopes -> ExtraScopes
    | `ReductionDontExposeCase -> ReductionDontExposeCase
    | `ReductionNeverUnfold -> ReductionNeverUnfold
    | `Rename -> Rename

  let _of (x : _t) : t = match x with
    | Assert -> `Assert
    | ClearBidiHint -> `ClearBidiHint
    | ClearImplicits -> `ClearImplicits
    | ClearScopes -> `ClearScopes
    | DefaultImplicits -> `DefaultImplicits
    | ExtraScopes -> `ExtraScopes
    | ReductionDontExposeCase -> `ReductionDontExposeCase
    | ReductionNeverUnfold -> `ReductionNeverUnfold
    | Rename -> `Rename

  let t_of_python x = _of (_t_of_python x)
  let python_of_t x = python_of__t (_to x)

end

type arguments_modifier =
  [%import: Vernacexpr.arguments_modifier]
  [@@deriving sexp,yojson]

let arguments_modifier_of_python = AM.t_of_python
let python_of_arguments_modifier = AM.python_of_t

type vernac_one_argument_status =
  [%import: Vernacexpr.vernac_one_argument_status]
  [@@deriving sexp,yojson,python]

type vernac_argument_status =
  [%import: Vernacexpr.vernac_argument_status]
  [@@deriving sexp,yojson,python]

type hint_info_expr =
  [%import: Vernacexpr.hint_info_expr]
  [@@deriving sexp,yojson,python]

type reference_or_constr =
  [%import: Vernacexpr.reference_or_constr]
  [@@deriving sexp,yojson,python]

type hints_expr =
  [%import: Vernacexpr.hints_expr]
  [@@deriving sexp,yojson,python]

type vernac_expr =
  [%import: Vernacexpr.vernac_expr]
  [@@deriving sexp, yojson, python]

type control_flag =
  [%import: Vernacexpr.control_flag]
  [@@deriving sexp, yojson, python]

type vernac_control_r =
  [%import: Vernacexpr.vernac_control_r]
  [@@deriving sexp, yojson, python]

type vernac_control =
  [%import: Vernacexpr.vernac_control]
  [@@deriving sexp, yojson, python]
