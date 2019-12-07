(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type private_constants = Safe_typing.private_constants
val private_constants_of_sexp : Sexp.t -> private_constants
val sexp_of_private_constants : private_constants -> Sexp.t

type global_declaration = Safe_typing.global_declaration
val global_declaration_of_sexp : Sexp.t -> global_declaration
val sexp_of_global_declaration : global_declaration -> Sexp.t

type side_effect_declaration = Safe_typing.side_effect_declaration
val side_effect_declaration_of_sexp : Sexp.t -> side_effect_declaration
val sexp_of_side_effect_declaration : side_effect_declaration -> Sexp.t
