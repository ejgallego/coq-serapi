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

module Names     = Ser_names
module Globnames = Ser_globnames
module Constr    = Ser_constr

(**********************************************************************)
(* Evar_kinds                                                         *)
(**********************************************************************)

type obligation_definition_status =
  [%import: Evar_kinds.obligation_definition_status]
  [@@deriving sexp]

type t =
  [%import: Evar_kinds.t]
  [@@deriving sexp]

