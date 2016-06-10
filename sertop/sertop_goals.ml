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

(* Taken from ide_slave *)
let process_goal sigma g =
  let env       = Goal.V82.env sigma g in
  let min_env   = Environ.reset_context env in
  let id        = Goal.uid g in
  let main_goal =
    let goal_constr = Reductionops.nf_evar sigma (Goal.V82.concl sigma g) in
    Constrextern.extern_type true env sigma goal_constr
  in
  let process_hyp d (env,l) =
    let d = Context.NamedList.Declaration.map_constr (Reductionops.nf_evar sigma) d in
    let d' = List.map (fun name -> let open Context.Named.Declaration in
                                   match Util.pi2 d with
                                   | None -> LocalAssum (name, Util.pi3 d)
                                   | Some value -> LocalDef (name, value, Util.pi3 d))
                      (Util.pi1 d) in
      (List.fold_right Environ.push_named d' env,
       (Richpp.richpp_of_pp (Printer.pr_var_list_decl env sigma d)) :: l) in

(* Improve this                                      *)
(* let pr_var_decl_skel pr_id env sigma (id,c,typ) = *)
(*   let pbody = match c with *)
(*     | None ->  (mt ()) *)
(*     | Some c -> *)
(* 	(\* Force evaluation *\) *)
(* 	let pb = pr_lconstr_env env sigma c in *)
(* 	let pb = if isCast c then surround pb else pb in *)
(* 	(str" := " ++ pb ++ cut () ) in *)
(*   let pt = pr_ltype_env env sigma typ in *)
(*   let ptyp = (str" : " ++ pt) in *)
(*   (pr_id id ++ hov 0 (pbody ++ ptyp)) *)
(*   hov 0 (pr_var_decl_skel (fun ids -> prlist_with_sep pr_comma pr_id ids) env sigma (l,c,typ)) *)

  let (_env, hyps) =
    Context.NamedList.fold process_hyp
      (Termops.compact_named_context (Environ.named_context env)) ~init:(min_env,[]) in
  (List.rev hyps, main_goal, id )

type goals_kind =
  | FgGoals
  | BgGoals
  | ShelvedGoals
  | GivenUpGoals
  [@@deriving sexp]

let get_internal_goals () =
  try
    let pfts = Proof_global.give_me_the_proof () in
    Some (Proof.map_structured_proof pfts process_goal)
  with Proof_global.NoCurrentProof -> None

let get_goals kind = match get_internal_goals () with
  | None -> []
  | Some g_if -> match kind with
    | FgGoals      -> g_if.Proof.fg_goals
    | BgGoals      -> (List.concat @@ List.map fst g_if.Proof.bg_goals) @
                      (List.concat @@ List.map snd g_if.Proof.bg_goals)
    | ShelvedGoals -> g_if.Proof.shelved_goals
    | GivenUpGoals -> g_if.Proof.given_up_goals
