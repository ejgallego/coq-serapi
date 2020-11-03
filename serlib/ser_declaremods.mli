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
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type 'a module_signature = 'a Declaremods.module_signature

val module_signature_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a module_signature
val sexp_of_module_signature : ('a -> Sexp.t) -> 'a module_signature -> Sexp.t
val module_signature_of_yojson : (Yojson.Safe.t -> ('a, string) Result.result) -> Yojson.Safe.t -> ('a module_signature, string) Result.result
val module_signature_to_yojson : ('a -> Yojson.Safe.t) -> 'a module_signature -> Yojson.Safe.t
val module_signature_of_python : (Py.Object.t -> 'a) -> Py.Object.t -> 'a module_signature
val python_of_module_signature : ('a -> Py.Object.t) -> 'a module_signature -> Py.Object.t

type inline = Declaremods.inline
val inline_of_sexp : Sexp.t -> inline
val sexp_of_inline : inline -> Sexp.t
val inline_of_yojson : Yojson.Safe.t -> (inline, string) Result.result
val inline_to_yojson : inline -> Yojson.Safe.t
val inline_of_python : Py.Object.t -> inline
val python_of_inline : inline -> Py.Object.t
