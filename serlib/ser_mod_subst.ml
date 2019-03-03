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

type delta_resolver =
  [%import: Mod_subst.delta_resolver]

let sexp_of_delta_resolver =
  Serlib_base.sexp_of_opaque ~typ:"Mod_subst.delta_resolver"

let delta_resolver_of_sexp =
  Serlib_base.opaque_of_sexp ~typ:"Mod_subst.delta_resolver"

type 'a substituted =
  [%import: 'a Mod_subst.substituted]

let sexp_of_substituted _ =
  Serlib_base.sexp_of_opaque ~typ:"Mod_subst.substituted"

let substituted_of_sexp _ =
  Serlib_base.opaque_of_sexp ~typ:"Mod_subst.substituted"
