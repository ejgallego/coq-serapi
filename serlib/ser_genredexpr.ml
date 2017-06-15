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

open Sexplib.Std

module Loc   = Ser_loc
module Names = Ser_names
module Util  = Ser_util
module Locus = Ser_locus

type 'a red_atom =
  [%import: 'a Genredexpr.red_atom]
  [@@deriving sexp]

type 'a glob_red_flag =
  [%import: 'a Genredexpr.glob_red_flag]
  [@@deriving sexp]

type ('a,'b,'c) red_expr_gen =
  [%import: ('a,'b,'c) Genredexpr.red_expr_gen]
  [@@deriving sexp]

type ('a,'b,'c) may_eval =
  [%import: ('a,'b,'c) Genredexpr.may_eval]
  [@@deriving sexp]

open Ser_libnames
open Ser_constrexpr
open Ser_misctypes

(* Helpers for raw_red_expr *)
type r_trm =
  [%import: Genredexpr.r_trm
  [@with
     Constrexpr.constr_expr := constr_expr;
  ]]
  [@@deriving sexp]

type r_cst =
  [%import: Genredexpr.r_cst
  [@with
    Libnames.reference := reference;
    Misctypes.or_by_notation := or_by_notation;
  ]]
  [@@deriving sexp]

type r_pat =
  [%import: Genredexpr.r_pat
  [@with
     Constrexpr.constr_expr := constr_expr;
     Constrexpr.constr_pattern_expr := constr_pattern_expr;
  ]]
  [@@deriving sexp]

type raw_red_expr =
  [%import: Genredexpr.raw_red_expr
  [@with
     Genredexpr.red_expr_gen := red_expr_gen;
  ]]
  [@@deriving sexp]

