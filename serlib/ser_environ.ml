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

open Sexplib.Conv

module Stdlib = Ser_stdlib
module CEphemeron = Ser_cEphemeron
module Range  = Ser_range
module Names  = Ser_names
module Constr = Ser_constr
module Univ   = Ser_univ
module Opaqueproof    = Ser_opaqueproof
module Retroknowledge = Ser_retroknowledge
module UGraph         = Ser_uGraph
module Declarations   = Ser_declarations

type lazy_val = [%import: Environ.lazy_val]
let sexp_of_lazy_val = Serlib_base.sexp_of_opaque ~typ:"Environ.lazy_val"

type stratification =
  [%import: Environ.stratification]
  [@@deriving sexp_of]

type rel_context_val =
  [%import: Environ.rel_context_val]
  [@@deriving sexp_of]

type named_context_val =
  [%import: Environ.named_context_val]
  [@@deriving sexp_of]

type link_info =
  [%import: Environ.link_info]
  [@@deriving sexp]

type key = 
  [%import: Environ.key]
  [@@deriving sexp]

type constant_key = 
  [%import: Environ.constant_key]
  [@@deriving sexp]

type mind_key =   
  [%import: Environ.mind_key]
  [@@deriving sexp]

type _globals = {
  env_constants : constant_key Names.Cmap_env.t;
  env_inductives : mind_key Names.Mindmap_env.t;
  env_modules : Declarations.module_body Names.MPmap.t;
  env_modtypes : Declarations.module_type_body Names.MPmap.t;
} [@@deriving sexp]

type globals = Environ.globals

let sexp_of_globals g = sexp_of__globals (Obj.magic g)
let _globals_of_sexp g = Obj.magic (_globals_of_sexp g)

type env =
  [%import: Environ.env]
  [@@deriving sexp_of]

let env_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Environ.env"

type ('constr, 'term) punsafe_judgment =
  [%import: ('constr, 'term) Environ.punsafe_judgment]
  [@@deriving sexp]

type unsafe_judgment =
  [%import: Environ.unsafe_judgment]
  [@@deriving sexp]
