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

type glob_level                       = Misctypes.glob_level
type glob_sort                        = Misctypes.glob_sort
type patvar                           = Misctypes.patvar
type 'a cast_type                     = 'a Misctypes.cast_type
type case_style                       = Misctypes.case_style

type 'constr intro_pattern_expr        = 'constr Misctypes.intro_pattern_expr
type intro_pattern_naming_expr         = Misctypes.intro_pattern_naming_expr
type 'constr intro_pattern_action_expr = 'constr Misctypes.intro_pattern_action_expr
type 'constr or_and_intro_pattern_expr = 'constr Misctypes.or_and_intro_pattern_expr

val glob_level_of_sexp : 'a -> 'b Misctypes.glob_sort_gen
val sexp_of_glob_level : 'a -> Sexp.t

val glob_sort_of_sexp : 'a -> 'b Misctypes.glob_sort_gen
val sexp_of_glob_sort : 'a -> Sexp.t

val patvar_of_sexp : 'a -> Names.Id.t
val sexp_of_patvar : 'a -> Sexp.t

val cast_type_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a cast_type
val sexp_of_cast_type : ('a -> Sexp.t) -> 'a cast_type -> Sexp.t

val case_style_of_sexp : Sexp.t -> case_style
val sexp_of_case_style : case_style -> Sexp.t

val intro_pattern_expr_of_sexp : (Sexp.t -> 'constr) -> Sexp.t -> 'constr intro_pattern_expr
val sexp_of_intro_pattern_expr : ('constr -> Sexp.t) -> 'constr intro_pattern_expr -> Sexp.t

val intro_pattern_naming_expr_of_sexp : Sexp.t -> intro_pattern_naming_expr
val sexp_of_intro_pattern_naming_expr : intro_pattern_naming_expr -> Sexp.t

val intro_pattern_action_expr_of_sexp : (Sexp.t -> 'constr) -> Sexp.t -> 'constr intro_pattern_action_expr
val sexp_of_intro_pattern_action_expr : ('constr -> Sexp.t) -> 'constr intro_pattern_action_expr -> Sexp.t

val or_and_intro_pattern_expr_of_sexp : (Sexp.t -> 'constr) -> Sexp.t -> 'constr or_and_intro_pattern_expr
val sexp_of_or_and_intro_pattern_expr : ('constr -> Sexp.t) -> 'constr or_and_intro_pattern_expr -> Sexp.t
