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
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

open Serlib

module Genintern = Ser_genintern
module Geninterp = Ser_geninterp

type ssrtermkind =
  [%import: Ssrmatching_plugin.Ssrmatching.ssrtermkind]
  [@@deriving sexp,yojson,hash,compare]

type cpattern =
  [%import: Ssrmatching_plugin.Ssrmatching.cpattern]
  [@@deriving sexp,yojson,hash,compare]

type ('a, 'b) ssrpattern =
  [%import: ('a, 'b) Ssrmatching_plugin.Ssrmatching.ssrpattern]
  [@@deriving sexp,yojson,hash,compare]

module PierceRPattern = struct

  type t = Ssrmatching_plugin.Ssrmatching.rpattern

  type _t = (cpattern, cpattern) ssrpattern
  [@@deriving sexp,yojson,hash,compare]
end

module B_ = SerType.Pierce(PierceRPattern)

type rpattern = B_.t
let sexp_of_rpattern = B_.sexp_of_t
let rpattern_of_sexp = B_.t_of_sexp
let rpattern_of_yojson = B_.of_yojson
let rpattern_to_yojson = B_.to_yojson
let hash_rpattern = B_.hash
let hash_fold_rpattern = B_.hash_fold_t
let compare_rpattern = B_.compare

type ssrdir =
  [%import: Ssrmatching_plugin.Ssrmatching.ssrdir]
  [@@deriving sexp]
