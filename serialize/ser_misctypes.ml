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

open Ser_names
open Ser_loc

type patvar = [%import: Misctypes.patvar]
let patvar_of_sexp = id_of_sexp
let sexp_of_patvar = sexp_of_id

type 'constr intro_pattern_expr =
  [%import: 'constr Misctypes.intro_pattern_expr
              [@with
                Names.Id.t := id;
              ]]
and intro_pattern_naming_expr   = [%import: Misctypes.intro_pattern_naming_expr
                                  [@with Names.Id.t := id;
                                  ]]
and 'constr intro_pattern_action_expr = [%import: 'constr Misctypes.intro_pattern_action_expr
                                  [@with Loc.t := loc;
                                  ]]
and 'constr or_and_intro_pattern_expr = [%import: 'constr Misctypes.or_and_intro_pattern_expr
                                  [@with Loc.t := loc;
                                  ]]
  [@@deriving sexp]

type 'id move_location =
  [%import: 'id Misctypes.move_location]
  [@@deriving sexp]

type 'a glob_sort_gen =
  [%import: 'a Misctypes.glob_sort_gen]
  [@@deriving sexp]

type sort_info =
  [%import: Misctypes.sort_info
  [@with
    Loc.t       := loc;
    Loc.located := located;
  ]]
  [@@deriving sexp]

type level_info =
  [%import: Misctypes.level_info
  [@with
    Loc.t       := loc;
    Loc.located := located;
  ]]
  [@@deriving sexp]

type glob_sort =
  [%import: Misctypes.glob_sort]
  [@@deriving sexp]

type glob_level =
  [%import: Misctypes.glob_level]
  [@@deriving sexp]

type case_style =
  [%import: Misctypes.case_style]
  [@@deriving sexp]

type 'a cast_type = [%import: 'a Misctypes.cast_type]
  [@@deriving sexp]

type quantified_hypothesis =
  [%import: Misctypes.quantified_hypothesis
  [@with
    Loc.t := loc;
    Names.Id.t := id;
  ]]
  [@@deriving sexp]

type 'a explicit_bindings =
  [%import: 'a Misctypes.explicit_bindings
  [@with
    Loc.t := loc;
  ]]
  [@@deriving sexp]

type 'a bindings =
  [%import: 'a Misctypes.bindings
  [@with
    Loc.t := loc;
    Names.Id.t := id;
  ]]
  [@@deriving sexp]

type 'a with_bindings =
  [%import: 'a Misctypes.with_bindings
  [@with
    Loc.t := loc;
  ]]
  [@@deriving sexp]

type 'a or_var =
  [%import: 'a Misctypes.or_var
  [@with
    Loc.t := loc;
    Loc.located := located;
    Names.Id.t := id;
  ]]
  [@@deriving sexp]

type 'a and_short_name =
  [%import: 'a Misctypes.and_short_name
  [@with
    Loc.t := loc;
    Loc.located := located;
    Names.Id.t := id;
  ]]
  [@@deriving sexp]

type 'a or_by_notation =
  [%import: 'a Misctypes.or_by_notation
  [@with
    Loc.t := loc;
  ]]
  [@@deriving sexp]

type module_kind =
  [%import: Misctypes.module_kind]
  [@@deriving sexp]

