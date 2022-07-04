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
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type hint_db_name = Hints.hint_db_name

val sexp_of_hint_db_name : hint_db_name -> Sexp.t
val hint_db_name_of_sexp : Sexp.t -> hint_db_name

type 'a hints_path_gen = 'a Hints.hints_path_gen

val sexp_of_hints_path_gen : ('a -> Sexp.t) -> 'a hints_path_gen -> Sexp.t
val hints_path_gen_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a hints_path_gen

type 'a hints_path_atom_gen = 'a Hints.hints_path_atom_gen

val sexp_of_hints_path_atom_gen : ('a -> Sexp.t) -> 'a hints_path_atom_gen -> Sexp.t
val hints_path_atom_gen_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a hints_path_atom_gen

type hints_path = Hints.hints_path

val sexp_of_hints_path : hints_path -> Sexp.t
val hints_path_of_sexp : Sexp.t -> hints_path

type 'a hints_transparency_target = 'a Hints.hints_transparency_target [@@deriving sexp,yojson,hash,compare]
type hint_mode = Hints.hint_mode [@@deriving sexp,yojson,hash,compare]
