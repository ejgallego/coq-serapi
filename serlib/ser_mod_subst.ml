(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

open Sexplib.Std

module Names = Ser_names

type delta_resolver =
  [%import: Mod_subst.delta_resolver]

let sexp_of_delta_resolver =
  Serlib_base.sexp_of_opaque ~typ:"Mod_subst.delta_resolver"

let delta_resolver_of_sexp =
  Serlib_base.opaque_of_sexp ~typ:"Mod_subst.delta_resolver"

(* type substitution = (Names.ModPath.t * delta_resolver) Names.Umap.t
 *   [@@deriving sexp] *)

type substitution =
  [%import: Mod_subst.substitution]

let sexp_of_substitution = Serlib_base.sexp_of_opaque ~typ:"Mod_subst.substitution"
let substitution_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Mod_subst.substitution"

type 'a _substituted = {
  mutable subst_value : 'a;
  mutable subst_subst : substitution list;
} [@@deriving sexp]

type 'a substituted =
  [%import: 'a Mod_subst.substituted]

let sexp_of_substituted f x = sexp_of__substituted f (Obj.magic x)
let substituted_of_sexp f x = Obj.magic (_substituted_of_sexp f x)
