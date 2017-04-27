(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* We ship our own type due to Context lack of support for anything
   other than Constr.t *)
type 'a hyp = (Names.Id.t list * 'a option * 'a)
type 'a reified_goal = { name: string; ty: 'a; hyp: 'a hyp list }

(* Ready to make into a GADT *)
val get_goals  : Stateid.t -> Constr.t               reified_goal Proof.pre_goals option
val get_egoals : Stateid.t -> Constrexpr.constr_expr reified_goal Proof.pre_goals option


