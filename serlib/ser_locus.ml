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
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Names     = Ser_names

type 'a or_var =
  [%import: 'a Locus.or_var]
  [@@deriving sexp,yojson,python,hash,compare]

type 'a occurrences_gen =
  [%import: 'a Locus.occurrences_gen]
  [@@deriving sexp,yojson,python,hash,compare]

type occurrences_expr =
  [%import: Locus.occurrences_expr]
  [@@deriving sexp,yojson,python,hash,compare]

type 'a with_occurrences =
  [%import: 'a Locus.with_occurrences]
  [@@deriving sexp,yojson,python,hash,compare]

type occurrences =
  [%import: Locus.occurrences]
  [@@deriving sexp,yojson]

type hyp_location_flag =
  [%import: Locus.hyp_location_flag]
  [@@deriving sexp,yojson,python,hash,compare]

type 'a hyp_location_expr =
  [%import: 'a Locus.hyp_location_expr]
  [@@deriving sexp,yojson,python,hash,compare]

type 'id clause_expr =
  [%import: 'id Locus.clause_expr]
  [@@deriving sexp,yojson,python,hash,compare]

type clause =
  [%import: Locus.clause]
  [@@deriving sexp]

type clause_atom =
  [%import: Locus.clause_atom]
  [@@deriving sexp]

type concrete_clause =
  [%import: Locus.concrete_clause]
  [@@deriving sexp]

type hyp_location =
  [%import: Locus.hyp_location]
  [@@deriving sexp,yojson,python,hash,compare]

type goal_location =
  [%import: Locus.goal_location]
  [@@deriving sexp]

type simple_clause =
  [%import: Locus.simple_clause]
  [@@deriving sexp]

type 'a or_like_first =
  [%import: 'a Locus.or_like_first]
  [@@deriving sexp]

