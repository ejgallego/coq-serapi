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

include SerType.SJHC with type t = Sorts.t

type family = Sorts.family [@@deriving sexp,yojson,hash,compare]
type relevance = Sorts.relevance [@@deriving sexp,yojson,hash,compare]

module QVar : sig
  include SerType.SJHC with type t = Sorts.QVar.t
  module Set : SerType.SJHC with type t = Sorts.QVar.Set.t
end

module Quality : sig
  type constant = Sorts.Quality.constant [@@deriving sexp,yojson,hash,compare]

  include SerType.SJHC with type t = Sorts.Quality.t
  module Set : SerType.SJHC with type t = Sorts.Quality.Set.t
end

module QConstraints : SerType.SJHC with type t = Sorts.QConstraints.t
