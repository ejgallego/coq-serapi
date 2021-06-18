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

type tag = Vmvalues.tag

val tag_of_sexp : Sexp.t -> tag
val sexp_of_tag : tag -> Sexp.t

type structured_constant = Vmvalues.structured_constant

val structured_constant_of_sexp : Sexp.t -> structured_constant
val sexp_of_structured_constant : structured_constant -> Sexp.t

type reloc_table = Vmvalues.reloc_table
val reloc_table_of_sexp : Sexp.t -> reloc_table
val sexp_of_reloc_table : reloc_table -> Sexp.t

type annot_switch = Vmvalues.annot_switch
val annot_switch_of_sexp : Sexp.t -> annot_switch
val sexp_of_annot_switch : annot_switch -> Sexp.t
