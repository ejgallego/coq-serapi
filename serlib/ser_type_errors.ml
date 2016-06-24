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

open Ser_constr
open Ser_environ
open Ser_names
open Ser_sorts
open Ser_univ

type arity_error =
  [%import: Type_errors.arity_error]
  [@@deriving sexp]

type guard_error =
  [%import: Type_errors.guard_error
  [@with
     Environ.env := env;
     Term.constr := constr;
  ]]
  [@@deriving sexp]

type type_error =
  [%import: Type_errors.type_error
  [@with
     Environ.env := env;
     Environ.unsafe_judgment := unsafe_judgment;
     Term.constr := constr;
     Term.types  := constr;
     Term.pinductive := pinductive;
     Term.pconstructor := pconstructor;
     Term.sorts_family := family;
     Term.case_info := case_info;
     Names.variable := id;
     Names.Name.t := name;
     Names.identifier := id;
     Univ.constraints := constraints;
  ]]
  [@@deriving sexp]

