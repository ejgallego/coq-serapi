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

let context_of_st m = match m with
  | Stm.Valid (Some { Vernacstate.lemmas = Some pstate; _ } ) ->
    Vernacstate.LemmaStack.with_top pstate
      ~f:Declare.Proof.get_current_context
  | _ ->
    let env = Global.env () in Evd.from_env env, env
