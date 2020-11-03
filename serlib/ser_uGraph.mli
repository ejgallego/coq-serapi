(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

open Sexplib

(* Use utils PJ *)
module Bound : sig
  type t = UGraph.Bound.t

  val sexp_of_t : t -> Sexp.t
  val t_of_sexp : Sexp.t -> t
  val python_of_t : t -> Py.Object.t
  val t_of_python : Py.Object.t -> t
end

type t = UGraph.t

val sexp_of_t : t -> Sexp.t
val t_of_sexp : Sexp.t -> t
val python_of_t : t -> Py.Object.t
val t_of_python : Py.Object.t -> t
