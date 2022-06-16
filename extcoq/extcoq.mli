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
(* Coq Extended API                                                     *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* Functions missing from Coq's API, to be upstreamed! *)
val context_of_st : Stm.state -> Evd.evar_map * Environ.env
