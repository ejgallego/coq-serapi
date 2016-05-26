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

(**********************************************************************)
(* Globnames.mli                                                      *)
(**********************************************************************)

open Ser_names

type global_reference = [%import: Globnames.global_reference
                        [@with Names.variable    := id;
                               Names.constant    := constant;
                               Names.inductive   := inductive;
                               Names.constructor := constructor;
                        ]]
                        [@@deriving sexp]

