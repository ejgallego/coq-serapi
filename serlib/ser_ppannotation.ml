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

open Ser_constrexpr
open Ser_ppextend
open Ser_tacexpr
open Ser_vernacexpr

type ppannotation =
  [%import: Ppannotation.t
  [@with
     Ppextend.unparsing       := unparsing;
     Constrexpr.constr_expr   := constr_expr;
     Vernacexpr.vernac_expr   := vernac_expr;

     Tacexpr.atomic_tactic_expr := atomic_tactic_expr;

     Tacexpr.raw_tactic_expr  := raw_tactic_expr;
     Tacexpr.raw_atomic_tactic_expr  := raw_atomic_tactic_expr;

     Tacexpr.glob_tactic_expr := glob_tactic_expr;
     Tacexpr.glob_atomic_tactic_expr := glob_atomic_tactic_expr;
  ]]
  [@@deriving sexp]

(* type t = *)
(*   | AKeyword *)
(*   | AUnparsing            of unparsing *)
(*   | AConstrExpr           of constr_expr *)
(*   | AVernac               of vernac_expr *)
(*   | AGlobTacticExpr       of glob_tactic_expr *)
(*   | AGlobAtomicTacticExpr of glob_atomic_tactic_expr *)
(*   | ARawTacticExpr        of raw_tactic_expr *)
(*   | ARawAtomicTacticExpr  of raw_atomic_tactic_expr *)
(*   | AAtomicTacticExpr     of atomic_tactic_expr *)
