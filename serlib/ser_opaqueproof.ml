(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

open Sexplib.Std
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

module Future = Ser_future
module Names  = Ser_names
module Univ   = Ser_univ
module Constr = Ser_constr
module Mod_subst = Ser_mod_subst
module Cooking = Ser_cooking

module OP = struct
type t = [%import: Opaqueproof.opaque]
type _t =
  | Indirect of Mod_subst.substitution list * Cooking.cooking_info list * Names.DirPath.t * int (* subst, discharge, lib, index *)
 [@@deriving sexp,yojson,hash,compare]
end

module B_ = SerType.Pierce(OP)

type opaque = Opaqueproof.opaque
let sexp_of_opaque = B_.sexp_of_t
let opaque_of_sexp = B_.t_of_sexp
let opaque_of_yojson = B_.of_yojson
let opaque_to_yojson = B_.to_yojson
let hash_opaque = B_.hash
let hash_fold_opaque = B_.hash_fold_t
let compare_opaque = B_.compare

module Map = Ser_cMap.Make(Int.Map)(Ser_int)

module OTSpec = struct
  type t = Opaqueproof.opaquetab
  type _t = {
    opaque_len : int;
    opaque_dir : Names.DirPath.t;
  } [@@deriving sexp,yojson,hash,compare]
end

module C_ = SerType.Pierce(OTSpec)

type opaquetab = C_.t
let sexp_of_opaquetab = C_.sexp_of_t
let opaquetab_of_sexp = C_.t_of_sexp
let opaquetab_of_yojson = C_.of_yojson
let opaquetab_to_yojson = C_.to_yojson
let hash_opaquetab = C_.hash
let hash_fold_opaquetab = C_.hash_fold_t
let compare_opaquetab = C_.compare
