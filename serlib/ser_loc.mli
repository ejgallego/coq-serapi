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

(**********************************************************************)
(* Loc.mli                                                            *)
(**********************************************************************)

open Sexplib

include SerType.SJP with type t = Loc.t

(* Don't print locations. Global-flag Hack. *)
val omit_loc : bool ref

type 'a located = 'a Loc.located
val located_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a Loc.located
val sexp_of_located : ('a -> Sexp.t) -> 'a Loc.located -> Sexp.t
val located_of_yojson : (Yojson.Safe.t -> ('a, string) Result.result) -> Yojson.Safe.t -> ('a located, string) Result.result
val located_to_yojson : ('a -> Yojson.Safe.t) -> 'a located -> Yojson.Safe.t
val located_of_python : (Py.Object.t -> 'a) -> Py.Object.t -> 'a Loc.located
val python_of_located : ('a -> Py.Object.t) -> 'a Loc.located -> Py.Object.t
