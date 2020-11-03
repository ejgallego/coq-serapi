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

type body_code = Vmemitcodes.body_code
val sexp_of_body_code : body_code -> Sexp.t
val body_code_of_sexp : Sexp.t -> body_code

(* type to_patch_substituted = Vmemitcodes.to_patch_substituted
 * 
 * val sexp_of_to_patch_substituted : to_patch_substituted -> Sexp.t
 * val to_patch_substituted_of_sexp : Sexp.t -> to_patch_substituted *)
(* val python_of_to_patch_substituted : to_patch_substituted -> Py.Object.t
 * val to_patch_substituted_of_python : Py.Object.t -> to_patch_substituted *)
