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

(** gets the constr associated to the type of the current goal *)
let get_goal_type
    (sigma : Evd.evar_map)
    (g : Goal.goal) : Constr.constr =
  (* XXX: Why does extern_type require both an env and an evar_map ? *)
  Reductionops.nf_evar sigma (Goal.V82.concl sigma g)

(** gets a hypothesis *)
let get_hyp
    (sigma : Evd.evar_map)
    (hdecl : Context.Compacted.Declaration.t) =
  Context.Compacted.Declaration.map_constr (Reductionops.nf_evar sigma) hdecl

type reified_goal = Constr.constr * Context.Compacted.Declaration.t list

let process_goal sigma g : reified_goal =
  let env       = Goal.V82.env sigma g                                      in
  (* why is compaction neccesary... ? *)
  let ctx       = Termops.compact_named_context (Environ.named_context env) in
  let hyps      = List.map (get_hyp sigma) ctx                              in
  (get_goal_type sigma g, hyps)

let get_goals sid : reified_goal Proof.pre_goals option =
  try begin
    match Stm.state_of_id sid with
    | `Expired | `Error _ -> None
    | `Valid ost ->
      Option.map (fun stm_st ->
          Proof.map_structured_proof (Proof_global.proof_of_state stm_st.Stm.proof) process_goal
        ) ost
  end
  with Proof_global.NoCurrentProof -> None

(* type reified_egoal = Constrexpr.constr_expr * (Names.Id.t list * Constrexpr.constr_expr option * Constrexpr.constr_expr) list *)
type reified_egoal = Constrexpr.constr_expr * unit list

(* let extern_hyp env sigma hyp = *)
  (* (names, _def, htype) = *)
  (* let ehtype = Constrextern.extern_constr true env sigma htype in *)
  (* (names, None, ehtype) *)

let process_egoal sigma g : reified_egoal =
  let env       = Goal.V82.env sigma g                                      in
  (* why is compaction neccesary... ? *)
  let goal      = get_goal_type sigma g                                     in
  let egoal     = Constrextern.extern_constr true env sigma goal            in
  (* let ctx       = Termops.compact_named_context (Environ.named_context env) in *)
  (* let hyps      = List.map (get_hyp sigma) ctx                              in *)
  (* let ehyps     = List.map (extern_hyp env sigma) hyps                      in *)
  (* XXX: Fixme *)
  (* (egoal, ehyps) *)
  (egoal, [])

let get_egoals sid : reified_egoal Proof.pre_goals option =
  try begin
    match Stm.state_of_id sid with
    | `Expired | `Error _ -> None
    | `Valid ost ->
      Option.map (fun stm_st ->
          Proof.map_structured_proof (Proof_global.proof_of_state stm_st.Stm.proof) process_egoal
        ) ost
  end
  with Proof_global.NoCurrentProof -> None
