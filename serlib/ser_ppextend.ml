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
open Ppx_python_runtime

module Loc           = Ser_loc
module Notation_term = Ser_notation_term
module Notation_gram = Ser_notation_gram
module Constrexpr    = Ser_constrexpr
module Extend        = Ser_extend

type ppbox =
  [%import: Ppextend.ppbox]
  [@@deriving sexp,yojson,python]

type ppcut =
  [%import: Ppextend.ppcut]
  [@@deriving sexp,yojson,python]

type pattern_quote_style =
  [%import: Ppextend.pattern_quote_style]
  [@@deriving sexp,yojson,python]

type unparsing =
  [%import: Ppextend.unparsing]
  [@@deriving sexp,python]

type unparsing_rule =
  [%import: Ppextend.unparsing_rule]
  [@@deriving sexp,python]

type extra_unparsing_rules =
  [%import: Ppextend.extra_unparsing_rules]
  [@@deriving sexp,python]

type notation_printing_rules =
  [%import: Ppextend.notation_printing_rules]
  [@@deriving sexp,python]
