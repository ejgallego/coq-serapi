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
(* Written by: Karl Palmskog                                            *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let fatal_exn exn info =
  let loc = Loc.get_loc info in
  let msg = Pp.(pr_opt_no_spc Topfmt.pr_loc loc ++ fnl ()
                ++ CErrors.iprint (exn, info)) in
  Format.eprintf "Error: @[%a@]@\n%!" Pp.pp_with msg;
  exit 1

let create_document ~in_file ~async ~async_workers ~quick ~iload_path ~debug =

  let open Sertop_init in

  (* coq initialization *)
  coq_init
    { fb_handler = (fun _ -> ())  (* XXXX *)
    ; ml_load    = None
    ; debug
    };

  (* document initialization *)

  let stm_options = process_stm_flags
      { enable_async  = async
      ; deep_edits    = false
      ; async_workers = async_workers
      } in

  (* Disable due to https://github.com/ejgallego/coq-serapi/pull/94 *)
  let stm_options =
    { stm_options with
      async_proofs_tac_error_resilience = `None
    ; async_proofs_cmd_error_resilience = false
    } in

  let stm_options =
    if quick
    then { stm_options with async_proofs_mode = APonLazy }
    else stm_options
  in

  let require_libs = ["Coq.Init.Prelude", None, Some false] in

  let ndoc = { Stm.doc_type = Stm.VoDoc in_file
             ; require_libs
             ; iload_path
             ; stm_options
             } in

  (* Workaround, see
     https://github.com/ejgallego/coq-serapi/pull/101 *)
  if quick || async <> None
  then Safe_typing.allow_delayed_constants := true;

  Stm.new_doc ndoc

exception End_of_input

let input_doc ~in_chan ~process ~doc ~sid =
  try while true; do
      let line = input_line in_chan in
      if String.trim line <> "" then process ~doc ~sid line
    done
  with End_of_file -> ()

let context_of_st m = match m with
  | `Valid (Some { Vernacstate.proof = Some pstate; _ } ) ->
    Pfedit.get_current_context pstate
  | _ ->
    let env = Global.env () in Evd.from_env env, env    

let str_pp_obj env sigma fmt (obj : Serapi_protocol.coq_object) : unit =
  Format.fprintf fmt "%a" Pp.pp_with (Serapi_protocol.gen_pp_obj env sigma obj)

let process_line ~pp ~doc ~sid line =
  let open Serapi_protocol in
  let st = Stm.state_of_id ~doc sid in
  let sigma, env = context_of_st st in
  let info = QueryUtil.info_of_id env line in
  let def = snd info in
  match def with
  | [CoqConstr def_term] ->
     let evd = Evd.from_env env in
     let edef_term = EConstr.of_constr def_term in
     let gdef_term = Detyping.detype Detyping.Now false Names.Id.Set.empty env evd edef_term in
     Format.pp_set_margin Format.std_formatter 100000;
     Format.printf "%s: %!" line;
     Format.fprintf Format.std_formatter "\"@[%a@]\" %!" (str_pp_obj env sigma) (CoqConstr def_term);
     Format.printf "@[%a@] %!" pp (Serlib.Ser_glob_term.sexp_of_glob_constr gdef_term);
     Format.printf "@[%a@]\n%!" pp (Serlib.Ser_constr.sexp_of_constr def_term)
  | _ -> ()

let check_pending_proofs ~pstate =
  Option.iter (fun pstate ->
  let pfs = Proof_global.get_all_proof_names pstate in
  if not CList.(is_empty pfs) then
    let msg = let open Pp in
      seq [ str "There are pending proofs: "
          ; pfs |> List.rev |> prlist_with_sep pr_comma Names.Id.print; str "."] in
    CErrors.user_err msg
  ) pstate

let close_document ~doc ~pstate =
  let _doc = Stm.join ~doc in
  check_pending_proofs ~pstate

let sername_version = Ser_version.ser_git_version

let sername_man =
  [
    `S "DESCRIPTION";
    `P "Experimental Coq name serializer.";
    `S "USAGE";
    `P "To serialize names listed in `n.txt`:";
    `Pre "sername -Q fs,Funs n.txt > n.sexp";
    `P "See the documentation on the project's webpage for more information."
  ]

let sername_doc = "sername Coq tool"

open Cmdliner

let driver debug printer async async_workers quick coq_path ml_path load_path rload_path in_file omit_loc omit_att exn_on_opaque =

  (* closures *)
  let pp = Sertop_ser.select_printer printer in
  let process = process_line ~pp in

  (* initialization *)
  let options = Serlib.Serlib_init.{ omit_loc; omit_att; exn_on_opaque } in
  Serlib.Serlib_init.init ~options;

  let iload_path = Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path @ ml_path @ load_path @ rload_path in
  let doc, sid = create_document ~in_file:"file.v" ~async ~async_workers ~quick ~iload_path ~debug in

  (* main loop *)
  let in_chan = open_in in_file in
  let () = input_doc ~in_chan ~process ~doc ~sid in (* XX *)
  let pstate = match Stm.state_of_id ~doc sid with
    | `Valid (Some { Vernacstate.proof; _ }) -> proof
    | _ -> None
  in
  let () = close_document ~doc ~pstate in
  ()

let main () =
  let input_file =
    let doc = "Input file." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:("FILE") ~doc)
  in

  let sername_cmd =
    let open Sertop_arg in
    Term.(const driver
          $ debug $ printer $ async $ async_workers $ quick $ prelude
          $ ml_include_path $ load_path $ rload_path $ input_file $ omit_loc $ omit_att $ exn_on_opaque
         ),
    Term.info "sername" ~version:sername_version ~doc:sername_doc ~man:sername_man
  in

  try match Term.eval ~catch:false sername_cmd with
    | `Error _ -> exit 1
    | _        -> exit 0
  with exn ->
    let (e, info) = CErrors.push exn in
    fatal_exn e info

let _ = main ()
