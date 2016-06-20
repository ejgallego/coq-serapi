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

open Sexplib.Std

type ltacprof_entry =
  [%import: Profile_ltac.ltacprof_entry]
  [@@deriving sexp]

type ltacprof_tactic =
  [%import: Profile_ltac.ltacprof_tactic]
  [@@deriving sexp]

type ltacprof_results =
  [%import: Profile_ltac.ltacprof_results]
  [@@deriving sexp]
