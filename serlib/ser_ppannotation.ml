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

module Constrexpr = Ser_constrexpr
module Ppextend   = Ser_ppextend
module Genarg     = Ser_genarg
module Tacexpr    = Ser_tacexpr
module Vernacexpr = Ser_vernacexpr

type t =
  [%import: Ppannotation.t]
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
