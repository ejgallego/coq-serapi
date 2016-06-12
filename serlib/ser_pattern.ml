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

open Ser_names
open Ser_globnames
open Ser_evar
open Ser_constr
open Ser_misctypes

type case_info_pattern =
  [%import: Pattern.case_info_pattern
  [@with
     Names.inductive      := inductive;
     Misctypes.case_style := case_style;
  ]]
  [@@deriving sexp]

type constr_pattern =
  [%import: Pattern.constr_pattern
  [@with
     Names.Id.t                 := id;
     Names.Name.t               := name;
     Names.projection           := projection;
     Globnames.global_reference := global_reference;
     Misctypes.existential_key  := evar;
     Misctypes.glob_sort        := glob_sort;
     Misctypes.patvar           := patvar;
     Term.fixpoint              := fixpoint;
     Term.cofixpoint            := cofixpoint;
  ]]
  [@@deriving sexp]
