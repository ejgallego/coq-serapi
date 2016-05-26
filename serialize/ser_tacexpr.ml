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

open Sexplib
(* open Sexplib.Std *)

(* open Ser_bigint *)
(* open Ser_loc *)
(* open Ser_names *)
(* open Ser_misctypes *)
(* open Ser_decl_kinds *)
(* open Ser_evar_kinds *)
(* open Ser_genarg *)
(* open Ser_libnames *)
(* open Ser_glob_term *)
(* open Ser_constrexpr *)

(* This is beyond import for the moment *)
(* type 'a gen_atomic_tactic_expr = [%import: 'a Tacexpr.gen_atomic_tactic_expr] *)
(*   [@@deriving sexp] *)

type raw_tactic_expr = Tacexpr.raw_tactic_expr

let raw_tactic_expr_of_sexp _rawt = Obj.magic 0
let sexp_of_raw_tactic_expr _sexp = Sexp.Atom ""

type raw_red_expr = Tacexpr.raw_red_expr

let raw_red_expr_of_sexp _rawt = Obj.magic 0
let sexp_of_raw_red_expr _sexp = Sexp.Atom ""
