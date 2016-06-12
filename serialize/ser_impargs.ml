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
open Sexplib.Std

open Ser_names

type argument_position =
  [%import: Impargs.argument_position]
  [@@deriving sexp]

type implicit_explanation =
  [%import: Impargs.implicit_explanation]
  [@@deriving sexp]

type maximal_insertion =
  [%import: Impargs.maximal_insertion]
  [@@deriving sexp]

type force_inference =
  [%import: Impargs.force_inference]
  [@@deriving sexp]

type implicit_side_condition = Impargs.implicit_side_condition

(* XXX *)
let implicit_side_condition_of_sexp _sexp : implicit_side_condition = Obj.magic 0
let sexp_of_implicit_side_condition _isc = Sexp.Atom "impSC"

type implicit_status =
  [%import: Impargs.implicit_status
  [@with
     Names.Id.t := id;
  ]]
  [@@deriving sexp]

type implicits_list =
  [%import: Impargs.implicits_list]
  [@@deriving sexp]




