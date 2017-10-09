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

module Loc = Ser_loc

type precedence =
  [%import: Ppextend.precedence]
  [@@deriving sexp]

type parenRelation =
  [%import: Ppextend.parenRelation]
  [@@deriving sexp]

type tolerability =
  [%import: Ppextend.tolerability]
  [@@deriving sexp]

type ppbox =
  [%import: Ppextend.ppbox]
  [@@deriving sexp]

type ppcut =
  [%import: Ppextend.ppcut]
  [@@deriving sexp]

type unparsing =
  [%import: Ppextend.unparsing]
  [@@deriving sexp]
