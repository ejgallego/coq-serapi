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

type retroknowledge =
  [%import: Retroknowledge.retroknowledge]

let sexp_of_retroknowledge = Serlib_base.sexp_of_opaque ~typ:"Retroknowledge.retroknowledge"
let retroknowledge_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Retroknowledge.retroknowledge"
