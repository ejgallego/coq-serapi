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
(* Written byo: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std

module Names = Ser_names
module CPrimitives = Ser_cPrimitives
module Mod_subst = Ser_mod_subst
module Vmvalues = Ser_vmvalues
module Vmbytecodes = Ser_vmbytecodes

type reloc_info =
  | Reloc_annot of Vmvalues.annot_switch
  | Reloc_const of Vmvalues.structured_constant
  | Reloc_getglobal of Names.Constant.t
  | Reloc_caml_prim of CPrimitives.t
 [@@deriving sexp]

type patches = {
  reloc_infos : (reloc_info * int array) array;
} [@@deriving sexp]

type emitcodes = string
  [@@deriving sexp]

type _to_patch = emitcodes * patches
  [@@deriving sexp]

type to_patch = Vmemitcodes.to_patch

let to_patch_of_sexp p = Obj.magic (_to_patch_of_sexp p)
let sexp_of_to_patch p = sexp_of__to_patch (Obj.magic p)

type body_code =
  [%import: Vmemitcodes.body_code]
  [@@deriving sexp]
