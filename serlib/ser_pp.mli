(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type t = Pp.t
type doc_view = Pp.doc_view

val t_of_sexp : Sexp.t -> t
val sexp_of_t : t -> Sexp.t
val of_yojson : Yojson.Safe.t -> (t, string) Result.result
val to_yojson : t -> Yojson.Safe.t
val t_of_python : Py.Object.t -> t
val python_of_t : t -> Py.Object.t

val doc_view_of_sexp : Sexp.t -> doc_view
val sexp_of_doc_view : doc_view -> Sexp.t
val doc_view_of_yojson : Yojson.Safe.t -> (doc_view, string) Result.result
val doc_view_to_yojson : doc_view -> Yojson.Safe.t
val doc_view_of_python : Py.Object.t -> doc_view
val python_of_doc_view : doc_view -> Py.Object.t
