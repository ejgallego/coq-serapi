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

open Sexplib.Std
open Ppx_python_runtime
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module ONames = Names
module CEphemeron = Ser_cEphemeron
module Names = Ser_names
module Constr  = Ser_constr
module Declarations = Ser_declarations
module Entries = Ser_entries
module Cooking = Ser_cooking
module Univ = Ser_univ

(* Side_effects *)
type certificate = {
  certif_struc : Declarations.structure_body;
  certif_univs : Univ.ContextSet.t;
} [@@deriving sexp,yojson,python,hash,compare]

type side_effect = {
  from_env : certificate CEphemeron.key;
  seff_constant : Names.Constant.t;
  seff_body : Declarations.constant_body;
} [@@deriving sexp,yojson,python,hash,compare]

module SeffOrd = struct
  type t = side_effect
  [@@deriving sexp,yojson,python,hash,compare]
end

module SeffSet = Set.Make(SeffOrd)
module SerSeffSet = Ser_cSet.Make(SeffSet)(SeffOrd)

module PC = struct
  (* t  private_constants *)
  type t = Safe_typing.private_constants
  type _t = { seff : side_effect list; elts : SerSeffSet.t }
  [@@deriving sexp,yojson,python,hash,compare]
end

module B_ = SerType.Pierce(PC)

type private_constants = Safe_typing.private_constants
let sexp_of_private_constants = B_.sexp_of_t
let private_constants_of_sexp = B_.t_of_sexp
let private_constants_of_yojson = B_.of_yojson
let private_constants_to_yojson = B_.to_yojson
let hash_private_constants = B_.hash
let hash_fold_private_constants = B_.hash_fold_t
let compare_private_constants = B_.compare

(*
type 'a effect_entry =
  [%import: 'a Safe_typing.effect_entry]
  [@@deriving sexp_of]

(* XXX: Typical GADT Problem *)
let _effect_entry_of_sexp (_f : Sexp.t -> 'a) (x : Sexp.t) : 'a effect_entry =
  let open Sexp in
  match x with
  | Atom "PureEntry" ->
    Obj__magic PureEntry
  | Atom "EffectEntry" ->
    Obj__magic EffectEntry
  | _ ->
    Sexplib.Conv_error.no_variant_match ()
*)

type global_declaration =
  [%import: Safe_typing.global_declaration]
  [@@deriving sexp]
