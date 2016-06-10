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

(** gets the constr associated to the type of the current goal *)
let get_goal_type
    (sigma : Evd.evar_map)
    (g : Goal.goal) : Constr.constr =
  (* XXX: Why does extern_type require both an env and an evar_map ? *)
  Reductionops.nf_evar sigma (Goal.V82.concl sigma g)

(** gets a hypothesis *)
let get_hyp
    (sigma : Evd.evar_map)
    (hdecl : Context.NamedList.Declaration.t) =
  Context.NamedList.Declaration.map_constr (Reductionops.nf_evar sigma) hdecl

type reified_goal = Constr.constr * Context.NamedList.Declaration.t list

let process_goal sigma g : reified_goal =
  let env       = Goal.V82.env sigma g                                      in
  (* why is compaction neccesary... ? *)
  let ctx       = Termops.compact_named_context (Environ.named_context env) in
  let hyps      = List.map (get_hyp sigma) ctx                              in
  (get_goal_type sigma g, hyps)

let get_goals () : reified_goal Proof.pre_goals option =
  try
    let proof = Proof_global.give_me_the_proof () in
    Some (Proof.map_structured_proof proof process_goal)
  with Proof_global.NoCurrentProof -> None
