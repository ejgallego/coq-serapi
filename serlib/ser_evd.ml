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

open Ser_environ
open Ser_reduction
open Ser_constr

type evar_constraint =
  [%import: Evd.evar_constraint
  [@with
     Environ.env := env;
     Term.constr := constr;
  ]]
  [@@deriving sexp]

type unsolvability_explanation =
  [%import: Evd.unsolvability_explanation]
  [@@deriving sexp]
