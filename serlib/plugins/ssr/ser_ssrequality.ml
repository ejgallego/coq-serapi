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

open Sexplib.Conv

module Ssrmatching_plugin = struct
  module Ssrmatching = Ser_ssrmatching
end

open Ssreflect_plugin

module Ssrast = Ser_ssrast

type ssrwkind =
  [%import: Ssrequality.ssrwkind]
  [@@deriving sexp]

type ssrrule =
  [%import: Ssrequality.ssrrule]
  [@@deriving sexp]

type ssrrwarg =
  [%import: Ssrequality.ssrrwarg]
  [@@deriving sexp]
