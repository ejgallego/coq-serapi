(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib
open Sexplib.Std

type level =
  [%import: Univ.Level.t]

type _level = ULevel of int
  [@@deriving sexp]

let _level_put level          = ULevel (Option.default 0 (Univ.Level.var_index level))
let _level_get (ULevel level) = Univ.Level.var level

let level_of_sexp sexp  = _level_get (_level_of_sexp sexp)
let sexp_of_level level = sexp_of__level (_level_put level)

(* XXX: Think what to do with this  *)
type universe =
  [%import: Univ.Universe.t]

(* type _universe                = Ser_Universe of  [@@deriving sexp] *)
(* let _universe_put  universe   = Ser_Universe (Universe.to_string universe) *)
(* let _universe_get (Ser_Universe universe) = Universe.of_string universe *)

(* let universe_of_sexp sexp     = _universe_get (_universe_of_sexp sexp) *)
(* let sexp_of_universe universe = sexp_of__universe (_universe_put universe) *)

let universe_of_sexp _sexp     = Univ.Universe.make (Univ.Level.prop)
let sexp_of_universe _universe = Sexp.Atom "UNIV"

(*************************************************************************)

type instance =
  [%import: Univ.Instance.t]

type _instance = Instance of level array
  [@@deriving sexp]

let _instance_put instance            = Instance (Univ.Instance.to_array instance)
let _instance_get (Instance instance) = Univ.Instance.of_array instance

let instance_of_sexp sexp     = _instance_get (_instance_of_sexp sexp)
let sexp_of_instance instance = sexp_of__instance (_instance_put instance)

type constraint_type =
  [%import: Univ.constraint_type]
  [@@deriving sexp]

type universe_instance =
  [%import: Univ.universe_instance
  [@with
    Instance.t := instance;
  ]]
  [@@deriving sexp]

type 'a puniverses =
  [%import: 'a Univ.puniverses]
  [@@deriving sexp]

