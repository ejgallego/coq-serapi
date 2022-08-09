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

(* open Sexplib.Std *)

module Names = Ser_names

module OD = struct
  type t = Mod_subst.delta_resolver
  let name = "Mod_subst.delta_resolver"
end

module A_ = SerType.Opaque(OD)

type delta_resolver = A_.t
let sexp_of_delta_resolver = A_.sexp_of_t
let delta_resolver_of_sexp = A_.t_of_sexp
let python_of_delta_resolver = A_.python_of_t
let delta_resolver_of_python = A_.t_of_python
let delta_resolver_of_yojson = A_.of_yojson
let delta_resolver_to_yojson = A_.to_yojson
let hash_delta_resolver = A_.hash
let hash_fold_delta_resolver = A_.hash_fold_t
let compare_delta_resolver = A_.compare

module OS = struct
  type t = Mod_subst.substitution
  let name = "Mod_subst.substitution"
end

module B_ = SerType.Opaque(OS)

type substitution = B_.t
let sexp_of_substitution = B_.sexp_of_t
let substitution_of_sexp = B_.t_of_sexp
let python_of_substitution = B_.python_of_t
let substitution_of_python = B_.t_of_python
let substitution_of_yojson = B_.of_yojson
let substitution_to_yojson = B_.to_yojson
let hash_substitution = B_.hash
let hash_fold_substitution = B_.hash_fold_t
let compare_substitution = B_.compare
