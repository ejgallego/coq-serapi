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

(**********************************************************************)
(* Misctypes.mli                                                      *)
(**********************************************************************)

open Sexplib

type patvar = Misctypes.patvar
val patvar_of_sexp : Sexp.t -> Names.Id.t
val sexp_of_patvar : Names.Id.t -> Sexp.t

type 'constr intro_pattern_expr = 'constr Misctypes.intro_pattern_expr
and intro_pattern_naming_expr   = Misctypes.intro_pattern_naming_expr
and 'constr intro_pattern_action_expr = 'constr Misctypes.intro_pattern_action_expr
and 'constr or_and_intro_pattern_expr = 'constr Misctypes.or_and_intro_pattern_expr

val intro_pattern_expr_of_sexp : (Sexp.t -> 'constr) -> Sexp.t -> 'constr intro_pattern_expr
val sexp_of_intro_pattern_expr : ('constr -> Sexp.t) -> 'constr intro_pattern_expr -> Sexp.t

val intro_pattern_naming_expr_of_sexp : Sexp.t -> intro_pattern_naming_expr
val sexp_of_intro_pattern_naming_expr : intro_pattern_naming_expr -> Sexp.t

val intro_pattern_action_expr_of_sexp : (Sexp.t -> 'constr) -> Sexp.t -> 'constr intro_pattern_action_expr
val sexp_of_intro_pattern_action_expr : ('constr -> Sexp.t) -> 'constr intro_pattern_action_expr -> Sexp.t

val or_and_intro_pattern_expr_of_sexp : (Sexp.t -> 'constr) -> Sexp.t -> 'constr or_and_intro_pattern_expr
val sexp_of_or_and_intro_pattern_expr : ('constr -> Sexp.t) -> 'constr or_and_intro_pattern_expr -> Sexp.t

type 'id move_location = 'id Misctypes.move_location

val move_location_of_sexp : (Sexp.t -> 'id) -> Sexp.t -> 'id move_location
val sexp_of_move_location : ('id -> Sexp.t) -> 'id move_location -> Sexp.t

type 'a glob_sort_gen = 'a Misctypes.glob_sort_gen

val glob_sort_gen_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a glob_sort_gen
val sexp_of_glob_sort_gen : ('a -> Sexp.t) -> 'a glob_sort_gen -> Sexp.t

type sort_info = Misctypes.sort_info
val sort_info_of_sexp : Sexp.t -> sort_info
val sexp_of_sort_info : sort_info -> Sexp.t

type level_info = Misctypes.level_info
val level_info_of_sexp : Sexp.t -> level_info
val sexp_of_level_info : level_info -> Sexp.t

type glob_sort = Misctypes.glob_sort
val glob_sort_of_sexp : Sexp.t -> glob_sort
val sexp_of_glob_sort : glob_sort -> Sexp.t

type glob_level = Misctypes.glob_level
val glob_level_of_sexp : Sexp.t -> glob_level
val sexp_of_glob_level : glob_level -> Sexp.t

(* Shadows the one in Constr. *)
type case_style = Misctypes.case_style
val case_style_of_sexp : Sexp.t -> case_style
val sexp_of_case_style : case_style -> Sexp.t

type 'a cast_type = 'a Misctypes.cast_type

val cast_type_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a cast_type
val sexp_of_cast_type : ('a -> Sexp.t) -> 'a cast_type -> Sexp.t

type existential_key = Misctypes.existential_key

val existential_key_of_sexp : Sexp.t -> existential_key
val sexp_of_existential_key : existential_key -> Sexp.t

type quantified_hypothesis = Misctypes.quantified_hypothesis

val quantified_hypothesis_of_sexp : Sexp.t -> quantified_hypothesis
val sexp_of_quantified_hypothesis : quantified_hypothesis -> Sexp.t

type 'a explicit_bindings = 'a Misctypes.explicit_bindings

val explicit_bindings_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a explicit_bindings
val sexp_of_explicit_bindings : ('a -> Sexp.t) -> 'a explicit_bindings -> Sexp.t

type 'a bindings = 'a Misctypes.bindings

val bindings_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a bindings
val sexp_of_bindings : ('a -> Sexp.t) -> 'a bindings -> Sexp.t

type 'a with_bindings = 'a Misctypes.with_bindings

val with_bindings_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a with_bindings
val sexp_of_with_bindings : ('a -> Sexp.t) -> 'a with_bindings -> Sexp.t

type 'a or_var = 'a Misctypes.or_var

val or_var_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a or_var
val sexp_of_or_var : ('a -> Sexp.t) -> 'a or_var -> Sexp.t

type 'a and_short_name = 'a Misctypes.and_short_name

val and_short_name_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a and_short_name
val sexp_of_and_short_name : ('a -> Sexp.t) -> 'a and_short_name -> Sexp.t

type 'a or_by_notation = 'a Misctypes.or_by_notation

val or_by_notation_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a or_by_notation
val sexp_of_or_by_notation : ('a -> Sexp.t) -> 'a or_by_notation -> Sexp.t

type module_kind = Misctypes.module_kind
val module_kind_of_sexp : Sexp.t -> module_kind
val sexp_of_module_kind : module_kind -> Sexp.t
