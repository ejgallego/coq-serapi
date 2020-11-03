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

type 'a t = 'a CAst.t = private {
  v   : 'a;
  loc : Loc.t option;
}

val t_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t
val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t

val of_yojson : (Yojson.Safe.t -> ('a, string) Result.result) -> Yojson.Safe.t -> ('a t, string) Result.result
val to_yojson : ('a -> Yojson.Safe.t) -> 'a t -> Yojson.Safe.t

val t_of_python : (Py.Object.t -> 'a) -> Py.Object.t -> 'a t
val python_of_t : ('a -> Py.Object.t) -> 'a t -> Py.Object.t

val omit_att : bool ref
