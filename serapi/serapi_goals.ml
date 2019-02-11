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
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

type 'a hyp = (Names.Id.t list * 'a option * 'a)
type 'a reified_goal = { name: string; ty: 'a; hyp: 'a hyp list }

type 'a ser_goals =
  { goals : 'a list
  ; stack : ('a list * 'a list) list
  ; shelf : 'a list
  ; given_up : 'a list
  }

(** XXX: Do we need to perform evar normalization? *)

module CDC = Context.Compacted.Declaration
type cdcl = Constr.compacted_declaration

let to_tuple ppx : cdcl -> (Names.Id.t list * 'pc option * 'pc) =
  let open CDC in function
    | LocalAssum(idl, tm)   -> (idl, None, ppx tm)
    | LocalDef(idl,tdef,tm) -> (idl, Some (ppx tdef), ppx tm)

(** gets a hypothesis *)
let get_hyp (ppx : Constr.t -> 'pc)
    (_sigma : Evd.evar_map)
    (hdecl : cdcl) : (Names.Id.t list * 'pc option * 'pc) =
  to_tuple ppx hdecl

(** gets the constr associated to the type of the current goal *)
let get_goal_type (ppx : Constr.t -> 'pc)
    (sigma : Evd.evar_map)
    (g : Goal.goal) =
  ppx @@ EConstr.to_constr sigma (Goal.V82.concl sigma g)

(** Generic processor  *)
let process_goal_gen ppx sigma g : 'a reified_goal =
  let env       = Goal.V82.env sigma g                                      in
  (* why is compaction neccesary... ? [eg for better display] *)
  let ctx       = Termops.compact_named_context (Environ.named_context env) in
  let ppx       = ppx env sigma                                             in
  let hyps      = List.map (get_hyp ppx sigma) ctx                          in
  { name = Goal.uid g; ty = get_goal_type ppx sigma g; hyp = hyps }

let get_goals_gen (ppx : Environ.env -> Evd.evar_map -> Constr.t -> 'a) ~doc sid
  : 'a reified_goal ser_goals option =
  try begin
    match Stm.state_of_id ~doc sid with
    | `Expired | `Error _ -> None
    | `Valid ost ->
      Option.map (fun stm_st ->
          let proof = Proof_global.proof_of_state stm_st.Vernacstate.proof in
          let Proof.{ goals; stack; shelf; given_up; sigma; _ } = Proof.data proof in
          let ppx = List.map (process_goal_gen ppx sigma) in
          { goals = ppx goals
          ; stack = List.map (fun (g1,g2) -> ppx g1, ppx g2) stack
          ; shelf = ppx shelf
          ; given_up = ppx given_up
          }
        ) ost
  end
  with Proof_global.NoCurrentProof -> None

let get_goals  = get_goals_gen (fun _ _ x -> x)
let get_egoals = get_goals_gen (fun env evd ec -> Constrextern.extern_constr true env evd EConstr.(of_constr ec))


