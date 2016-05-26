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
open Sexplib.Sexp

open Ser_names
open Ser_loc

open Misctypes

(* type 'a glob_sort_gen = GProp | GSet | GType of 'a *)

type glob_level = [%import: Misctypes.glob_level]
let glob_level_of_sexp _x = GProp
let sexp_of_glob_level _x = Atom ""

type glob_sort = [%import: Misctypes.glob_sort]
let glob_sort_of_sexp _x = GProp
let sexp_of_glob_sort _x = Atom ""

type patvar = [%import: Misctypes.patvar]
let patvar_of_sexp = id_of_sexp
let sexp_of_patvar = sexp_of_id

type 'a cast_type = [%import: 'a Misctypes.cast_type]
  [@@deriving sexp]

type case_style = [%import: Misctypes.case_style]
                [@@deriving sexp]

type 'constr intro_pattern_expr = [%import: 'constr Misctypes.intro_pattern_expr
                                  [@with Names.Id.t := id;
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

type 'a or_by_notation = [%import: 'a Misctypes.or_by_notation
    [@with Loc.t := loc;
    ]]
[@@deriving sexp]
