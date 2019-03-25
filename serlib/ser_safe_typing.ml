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

open Sexplib

module Entries = Ser_entries
module Cooking = Ser_cooking

(* This is easy to fix, it is just Term_typing.side_effects *)
type private_constants = Safe_typing.private_constants

let sexp_of_private_constants _ =
  Serlib_base.sexp_of_opaque ~typ:"Safe_typing.private_constants"
let private_constants_of_sexp _ =
  Serlib_base.opaque_of_sexp ~typ:"Safe_typing.private_constants"

type 'a effect_entry =
  [%import: 'a Safe_typing.effect_entry]
  [@@deriving sexp_of]

(* XXX: Typical GADT Problem *)
let effect_entry_of_sexp (_f : Sexp.t -> 'a) (x : Sexp.t) : 'a effect_entry =
  let open Sexp in
  match x with
  | Atom "PureEntry" ->
    Obj.magic PureEntry
  | Atom "EffectEntry" ->
    Obj.magic EffectEntry
  | _ ->
    Sexplib.Conv_error.no_variant_match ()

type global_declaration =
  [%import: Safe_typing.global_declaration]
  [@@deriving sexp_of]

(* XXX: Typical existential type problem *)
let global_declaration_of_sexp (x : Sexp.t) =
  let open Sexp in
  match x with
  | List [Atom "ConstantEntry"; ef; ce] ->
    (* This not sound, we should match on ef and pass the right
       serializer for the private constants *)
    ConstantEntry (effect_entry_of_sexp (fun x -> x) ef,
                   Entries.constant_entry_of_sexp (fun x -> x) ce)
  | List [Atom "GlobalRecipe"; cr] ->
    GlobalRecipe (Cooking.recipe_of_sexp cr)
  | _ ->
    Sexplib.Conv_error.no_variant_match ()
