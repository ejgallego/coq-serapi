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

module Variance : SerType.SJHC with type t = UVars.Variance.t

module Instance : SerType.SJHC with type t = UVars.Instance.t

module UContext : SerType.SJHC with type t = UVars.UContext.t

module AbstractContext : SerType.SJHC with type t = UVars.AbstractContext.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a UVars.in_universe_context
val in_universe_context_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a in_universe_context
val sexp_of_in_universe_context : ('a -> Sexp.t) -> 'a in_universe_context -> Sexp.t

type 'a puniverses = 'a * Instance.t
 [@@deriving sexp,yojson,hash,compare]
