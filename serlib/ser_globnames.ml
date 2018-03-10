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
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(**********************************************************************)
(* Globnames.mli                                                      *)
(**********************************************************************)

module Names = Ser_names

type global_reference = Names.global_reference
let global_reference_of_sexp = Names.global_reference_of_sexp
let sexp_of_global_reference = Names.sexp_of_global_reference

