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

type family = Sorts.family
val family_of_sexp : Sexp.t -> family
val sexp_of_family : family -> Sexp.t

val family_of_yojson : Yojson.Safe.t -> (family, string) Result.result
val family_to_yojson : family -> Yojson.Safe.t

include SerType.SJ with type t = Sorts.t

type relevance = Sorts.relevance
val relevance_of_sexp : Sexp.t -> relevance
val sexp_of_relevance : relevance -> Sexp.t
val relevance_of_yojson : Yojson.Safe.t -> (relevance, string) Result.result
val relevance_to_yojson : relevance -> Yojson.Safe.t
