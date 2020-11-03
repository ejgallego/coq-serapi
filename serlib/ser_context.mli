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

type 'a binder_annot = 'a Context.binder_annot
val binder_annot_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a binder_annot
val sexp_of_binder_annot : ('a -> Sexp.t) -> 'a binder_annot -> Sexp.t

val binder_annot_of_yojson : (Yojson.Safe.t -> ('a, string) Result.result) -> Yojson.Safe.t -> ('a binder_annot, string) Result.result
val binder_annot_to_yojson : ('a -> Yojson.Safe.t) -> 'a binder_annot -> Yojson.Safe.t

val binder_annot_of_python : (Py.Object.t -> 'a) -> Py.Object.t -> 'a binder_annot
val python_of_binder_annot : ('a -> Py.Object.t) -> 'a binder_annot -> Py.Object.t

module Rel : sig
  module Declaration : sig

    type ('c,'t) pt = ('c,'t) Context.Rel.Declaration.pt

    val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
    val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

    val pt_of_python : (Py.Object.t -> 'c) -> (Py.Object.t -> 't) -> Py.Object.t -> ('c,'t) pt
    val python_of_pt : ('c -> Py.Object.t) -> ('t -> Py.Object.t) -> ('c,'t) pt -> Py.Object.t

  end

  type ('c, 't) pt = ('c,'t) Context.Rel.pt

  val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
  val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

  val pt_of_python : (Py.Object.t -> 'c) -> (Py.Object.t -> 't) -> Py.Object.t -> ('c,'t) pt
  val python_of_pt : ('c -> Py.Object.t) -> ('t -> Py.Object.t) -> ('c,'t) pt -> Py.Object.t

end

module Named : sig

  module Declaration : sig

    type ('c, 't) pt = ('c, 't) Context.Named.Declaration.pt

    val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
    val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

    val pt_of_python : (Py.Object.t -> 'c) -> (Py.Object.t -> 't) -> Py.Object.t -> ('c,'t) pt
    val python_of_pt : ('c -> Py.Object.t) -> ('t -> Py.Object.t) -> ('c,'t) pt -> Py.Object.t

  end

  type ('c, 't) pt = ('c, 't) Context.Named.pt

  val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
  val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

  val pt_of_python : (Py.Object.t -> 'c) -> (Py.Object.t -> 't) -> Py.Object.t -> ('c,'t) pt
  val python_of_pt : ('c -> Py.Object.t) -> ('t -> Py.Object.t) -> ('c,'t) pt -> Py.Object.t

end

module Compacted : sig

  module Declaration : sig

    type ('c, 't) pt = ('c, 't) Context.Compacted.Declaration.pt
    val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
    val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

  end

  type ('c, 't) pt = ('c, 't) Context.Compacted.pt
  val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
  val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

end
