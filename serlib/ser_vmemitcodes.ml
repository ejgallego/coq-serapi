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

(* open Sexplib *)
module Names = Ser_names
module Mod_subst = Ser_mod_subst

[@@@ocaml.warning "-37"]

type emitcodes = String.t
(* [@@deriving sexp] *)

type reloc_info =
  | Reloc_annot of Vmvalues.annot_switch
  | Reloc_const of Vmvalues.structured_constant
  | Reloc_getglobal of Names.Constant.t
  | Reloc_proj_name of Names.Projection.Repr.t

type patches = {
  reloc_infos : (reloc_info * int array) array;
}

type to_patch = emitcodes * patches * Vmbytecodes.fv
(* [@@deriving sexp] *)

type _to_patch_substituted =
| PBCdefined of to_patch Mod_subst.substituted
| PBCalias of Names.Constant.t Mod_subst.substituted
| PBCconstant
(* [@@deriving sexp] *)

type to_patch_substituted =
  [%import: Vmemitcodes.to_patch_substituted]

let sexp_of_to_patch_substituted =
  Serlib_base.sexp_of_opaque ~typ:"Cemitcodes.to_patch_substituted"

(* XXX: Dummy value *)
let to_patch_substituted_of_sexp _ =
  Obj.magic PBCconstant
  (* Serlib_base.opaque_of_sexp ~typ:"Cemitcodes.to_patch_substituted" *)
