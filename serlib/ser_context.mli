(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

module Rel : sig
  module Declaration : sig

    type t = Context.Rel.Declaration.t
    val t_of_sexp : Sexp.t -> t
    val sexp_of_t : t -> Sexp.t

  end

  type t = Context.Rel.t
  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module Named : sig

  module Declaration : sig

    type t = Context.Named.Declaration.t
    val t_of_sexp : Sexp.t -> t
    val sexp_of_t : t -> Sexp.t

  end

  type t = Context.Named.t
  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end
