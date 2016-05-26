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

type contents = Sorts.contents

val contents_of_sexp : Sexp.t -> contents
val sexp_of_contents : contents -> Sexp.t

type family = Sorts.family
val family_of_sexp : Sexp.t -> family
val sexp_of_family : family -> Sexp.t

type sort = Sorts.t

val sort_of_sexp : Sexp.t -> sort
val sexp_of_sort : sort -> Sexp.t
