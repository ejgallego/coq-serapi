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

open Sexplib
open Sexplib.Std

module Range  = Ser_range
module Names  = Ser_names
module Constr = Ser_constr
module Opaqueproof    = Ser_opaqueproof
module Retroknowledge = Ser_retroknowledge
module UGraph         = Ser_uGraph
module Declarations   = Ser_declarations

type lazy_val = [%import: Environ.lazy_val]
(* let lazy_val_of_sexp _env  = Obj.magic 0 *)
let sexp_of_lazy_val _sexp = Sexp.Atom "Lazy Val"

type stratification =
  [%import: Environ.stratification]
  [@@deriving sexp_of]

type rel_context_val =
  [%import: Environ.rel_context_val]
  [@@deriving sexp_of]

type named_context_val =
  [%import: Environ.named_context_val]
  [@@deriving sexp_of]

type globals =
  [%import: Environ.globals]

let sexp_of_globals _sexp = Sexp.Atom "Globals"

type env =
  [%import: Environ.env]
  [@@deriving sexp_of]

let env_of_sexp _sexp = Obj.magic 0

type ('constr, 'term) punsafe_judgment =
  [%import: ('constr, 'term) Environ.punsafe_judgment]
  [@@deriving sexp]

type unsafe_judgment =
  [%import: Environ.unsafe_judgment]
  [@@deriving sexp]

