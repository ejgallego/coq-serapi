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

open Sexplib.Std

module Loc = Ser_loc
module Names = Ser_names
module Univ  = Ser_univ
module Evar  = Ser_evar
module Libnames = Ser_libnames

type patvar = [%import: Misctypes.patvar]
let patvar_of_sexp = Names.Id.t_of_sexp
let sexp_of_patvar = Names.Id.sexp_of_t

type 'constr intro_pattern_expr = [%import: 'constr Misctypes.intro_pattern_expr]
and intro_pattern_naming_expr   = [%import: Misctypes.intro_pattern_naming_expr]
and 'constr intro_pattern_action_expr = [%import: 'constr Misctypes.intro_pattern_action_expr]
and 'constr or_and_intro_pattern_expr = [%import: 'constr Misctypes.or_and_intro_pattern_expr]
  [@@deriving sexp]

type 'id move_location =
  [%import: 'id Misctypes.move_location]
  [@@deriving sexp]

type 'a glob_sort_gen =
  [%import: 'a Misctypes.glob_sort_gen]
  [@@deriving sexp]


type sort_info =
  [%import: Misctypes.sort_info]
  [@@deriving sexp]

type 'a universe_kind =
  [%import: 'a Misctypes.universe_kind]
  [@@deriving sexp]

type level_info =
  [%import: Misctypes.level_info]
  [@@deriving sexp]

type glob_sort =
  [%import: Misctypes.glob_sort]
  [@@deriving sexp]

type glob_level =
  [%import: Misctypes.glob_level]
  [@@deriving sexp]

(* Shadows the one in Constr. *)
type case_style =
  [%import: Misctypes.case_style]
  [@@deriving sexp]

type 'a cast_type = [%import: 'a Misctypes.cast_type]
  [@@deriving sexp]

type glob_constraint =
  [%import: Misctypes.glob_constraint]
  [@@deriving sexp]

type existential_key =
  [%import: Misctypes.existential_key]
  [@@deriving sexp]

type quantified_hypothesis =
  [%import: Misctypes.quantified_hypothesis]
  [@@deriving sexp]

type 'a explicit_bindings =
  [%import: 'a Misctypes.explicit_bindings]
  [@@deriving sexp]

type 'a bindings =
  [%import: 'a Misctypes.bindings]
  [@@deriving sexp]

type 'a with_bindings =
  [%import: 'a Misctypes.with_bindings]
  [@@deriving sexp]

type 'a or_var =
  [%import: 'a Misctypes.or_var]
  [@@deriving sexp]

type 'a and_short_name =
  [%import: 'a Misctypes.and_short_name]
  [@@deriving sexp]

type 'a or_by_notation =
  [%import: 'a Misctypes.or_by_notation]
  [@@deriving sexp]

type module_kind =
  [%import: Misctypes.module_kind]
  [@@deriving sexp]

type clear_flag =
  [%import: Misctypes.clear_flag]
  [@@deriving sexp]

type multi =
  [%import: Misctypes.multi]
  [@@deriving sexp]

type 'a core_destruction_arg =
  [%import: 'a Misctypes.core_destruction_arg]
  [@@deriving sexp]

type 'a destruction_arg =
  [%import: 'a Misctypes.destruction_arg]
  [@@deriving sexp]

type inversion_kind =
  [%import: Misctypes.inversion_kind]
  [@@deriving sexp]

type ('a,'b) gen_universe_decl =
  [%import: ('a,'b) Misctypes.gen_universe_decl]
  [@@deriving sexp]

