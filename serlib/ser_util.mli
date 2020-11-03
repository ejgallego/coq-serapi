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

type ('a, 'b) union = ('a, 'b) Util.union

val union_of_sexp : (Sexp.t -> 'a) -> (Sexp.t -> 'b) -> Sexp.t -> ('a, 'b) union
val sexp_of_union : ('a -> Sexp.t) -> ('b -> Sexp.t) -> ('a, 'b) union -> Sexp.t
val union_of_yojson : (Yojson.Safe.t -> ('a, string) Result.result) -> (Yojson.Safe.t -> ('b, string) Result.result) -> Yojson.Safe.t -> (('a, 'b) union, string) Result.result
val union_to_yojson : ('a -> Yojson.Safe.t) -> ('b -> Yojson.Safe.t) -> ('a,'b) union -> Yojson.Safe.t
val union_of_python : (Py.Object.t -> 'a) -> (Py.Object.t -> 'b) -> Py.Object.t -> ('a, 'b) union
val python_of_union : ('a -> Py.Object.t) -> ('b -> Py.Object.t) -> ('a, 'b) union -> Py.Object.t
