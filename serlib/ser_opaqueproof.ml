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

type proofterm = (Constr.constr * Univ.ContextSet.t) Future.computation
  [@@deriving sexp]

module OP = struct
type 'a t = [%import: 'a Opaqueproof.opaque]
type 'cooking_info _t =
  | Indirect of Mod_subst.substitution list * 'cooking_info list * Names.DirPath.t * int
 [@@deriving sexp,yojson,hash,compare]
end

module B_ = SerType.Pierce1(OP)
type 'c opaque = 'c B_.t
 [@@deriving sexp,yojson,hash,compare]

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
 [@@deriving sexp,yojson,hash,compare]
