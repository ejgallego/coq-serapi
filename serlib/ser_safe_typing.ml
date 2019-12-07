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

module ONames = Names
module CEphemeron = Ser_cEphemeron
module Names = Ser_names
module Constr  = Ser_constr
module Declarations = Ser_declarations
module Entries = Ser_entries
module Cooking = Ser_cooking

(* Side_effects *)
type side_effect = {
  from_env : Declarations.structure_body CEphemeron.key;
  seff_constant : Names.Constant.t;
  seff_body : Constr.t Declarations.constant_body;
} [@@deriving sexp]

module SeffOrd = struct
  type t = side_effect
  let compare e1 e2 = ONames.Constant.CanOrd.compare e1.seff_constant e2.seff_constant
  let t_of_sexp = side_effect_of_sexp
  let sexp_of_t = sexp_of_side_effect
end

module SeffSet = Set.Make(SeffOrd)
module SerSeffSet = Ser_cSet.Make(SeffSet)(SeffOrd)

type _t = { seff : side_effect list; elts : SerSeffSet.t }
 [@@deriving sexp]

type _private_constants = _t
 [@@deriving sexp]

type private_constants = Safe_typing.private_constants

let sexp_of_private_constants x = sexp_of__private_constants (Obj.magic x)
let private_constants_of_sexp x = Obj.magic (_private_constants_of_sexp x)

(*
type 'a effect_entry =
  [%import: 'a Safe_typing.effect_entry]
  [@@deriving sexp_of]

(* XXX: Typical GADT Problem *)
let _effect_entry_of_sexp (_f : Sexp.t -> 'a) (x : Sexp.t) : 'a effect_entry =
  let open Sexp in
  match x with
  | Atom "PureEntry" ->
    Obj.magic PureEntry
  | Atom "EffectEntry" ->
    Obj.magic EffectEntry
  | _ ->
    Sexplib.Conv_error.no_variant_match ()
*)

type global_declaration =
  [%import: Safe_typing.global_declaration]
  [@@deriving sexp]
