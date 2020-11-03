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

[@@@ocaml.warning "-37"]

type _emitcodes = string
  [@@deriving sexp]

type emitcodes = Vmemitcodes.emitcodes

let sexp_of_emitcodes x = sexp_of__emitcodes (Obj.magic x)
let emitcodes_of_sexp x = Obj.magic (_emitcodes_of_sexp x)

type reloc_info =
  | Reloc_annot of Vmvalues.annot_switch
  | Reloc_const of Vmvalues.structured_constant
  | Reloc_getglobal of Names.Constant.t
  | Reloc_proj_name of Names.Projection.Repr.t
  | Reloc_caml_prim of CPrimitives.t
 [@@deriving sexp]

type _patches = {
  reloc_infos : (reloc_info * int array) array;
} [@@deriving sexp]

type patches = Vmemitcodes.patches

let patches_of_sexp p = Obj.magic (_patches_of_sexp p)
let sexp_of_patches p = sexp_of__patches (Obj.magic p)

type to_patch = emitcodes * patches * Vmbytecodes.fv
  [@@deriving sexp]

type body_code =
  [%import: Vmemitcodes.body_code]
  [@@deriving sexp]

(* type _to_patch_substituted =
 * | PBCdefined of to_patch Mod_subst.substituted
 * | PBCalias of Names.Constant.t Mod_subst.substituted
 * | PBCconstant *)
(* [@@deriving sexp] *)

(* type to_patch_substituted =
 *   [%import: Vmemitcodes.to_patch_substituted]
 * 
 * let sexp_of_to_patch_substituted =
 *   Serlib_base.sexp_of_opaque ~typ:"Cemitcodes.to_patch_substituted"
 * 
 * (\* XXX: Dummy value *\)
 * let to_patch_substituted_of_sexp _ =
 *   Obj.magic PBCconstant
 *   (\* Serlib_base.opaque_of_sexp ~typ:"Cemitcodes.to_patch_substituted" *\) *)
