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
  let msg = Pp.(pr_opt_no_spc Loc.pr loc ++ fnl ()
                ++ CErrors.iprint (exn, info)) in
  Format.eprintf "Error: @[%a@]@\n%!" Pp.pp_with msg;
  exit 1

let create_document ~require_lib ~in_file ~stm_flags ~quick ~ml_load_path ~vo_load_path ~debug ~allow_sprop =

  let open Sertop.Sertop_init in

  (* coq initialization *)
  coq_init
    { fb_handler = (fun _ _ -> ())  (* XXXX *)
    ; ml_load    = None
    ; debug
    ; allow_sprop
    ; indices_matter = false
    ; ml_path = ml_load_path
    ; vo_path = vo_load_path
    } Format.std_formatter;

  (* document initialization *)

  let stm_options = process_stm_flags stm_flags in

  let stm_options =
    { stm_options with
      async_proofs_tac_error_resilience = FNone
    ; async_proofs_cmd_error_resilience = false
    } in

  (* Disable due to https://github.com/ejgallego/coq-serapi/pull/94 *)
  let stm_options =
    { stm_options with
      async_proofs_tac_error_resilience = FNone
    ; async_proofs_cmd_error_resilience = false
    } in

  let stm_options =
    if quick
    then { stm_options with async_proofs_mode = APonLazy }
    else stm_options
  in

  (*
  let require_libs =
    let prelude = ["Coq.Init.Prelude", None, Some false] in
    match require_lib with
    | Some l -> prelude @ [l, None, Some false]
    | None -> prelude
  in
  *)

  let injections = [Coqargs.RequireInjection ("Coq.Init.Prelude", None, Some false)] in

  let ndoc = { Stm.doc_type = Stm.VoDoc in_file
             ; injections
             ; stm_options
             } in

  (* Workaround, see
     https://github.com/ejgallego/coq-serapi/pull/101 *)
  if quick || stm_flags.enable_async <> None
  then Safe_typing.allow_delayed_constants := true;

  match require_lib with
  | None -> Stm.new_doc ndoc
  | Some l ->
     (*
     let sdoc = Stm.new_doc ndoc in
     let dir,from,exp = l,None,Some false in
     let mp = Libnames.qualid_of_string dir in
     let mfrom = Option.map Libnames.qualid_of_string from in
     Flags.silently (Vernacentries.vernac_require mfrom exp) [mp];
     sdoc
     *)
     let doc,sid = Stm.new_doc ndoc in
     let sent = Printf.sprintf "Require %s." l in
     let in_strm = Serapi.Ser_stream.of_string sent in
     let in_pa = Pcoq.Parsable.make ~loc:(Loc.initial (InFile { dirpath = None; file = in_file})) in_strm in
     match Stm.parse_sentence ~doc ~entry:Pvernac.main_entry sid in_pa with
     | Some ast ->
	let doc, sid, tip = Stm.add ~doc ~ontop:sid false ast in
	if tip <> NewAddTip then CErrors.user_err ?loc:ast.loc Pp.(str "fatal, got no `NewTip`");
	doc, sid
     | None -> assert false

exception End_of_input

let input_doc ~in_chan ~process ~doc ~sid =
  try while true; do
      let line = input_line in_chan in
      if String.trim line <> "" then process ~doc ~sid line
    done
  with End_of_file -> ()

let context_of_st m = match m with
  | Stm.Valid (Some { Vernacstate.lemmas = Some pstate; _ } ) ->
    Vernacstate.LemmaStack.with_top pstate
      ~f:Declare.Proof.get_current_context
  | _ ->
    let env = Global.env () in Evd.from_env env, env

let str_pp_obj env sigma fmt (obj : Serapi.Serapi_protocol.coq_object) : unit =
  Format.fprintf fmt "%a" Pp.pp_with (Serapi.Serapi_protocol.gen_pp_obj env sigma obj)

let process_line ~pp ~str_pp ~de_bruijn ~body ~doc ~sid line =
  let open Serapi.Serapi_protocol in
  let st = Stm.state_of_id ~doc sid in
  let sigma, env = context_of_st st in
  let info = QueryUtil.info_of_id env line in
  let def = if body then fst info else snd info in
  match def with
  | [CoqConstr def_term] ->
     let evd = Evd.from_env env in
     let edef_term = EConstr.of_constr def_term in
     let gdef_term = Detyping.detype Detyping.Now false Names.Id.Set.empty env evd edef_term in
     Format.pp_set_margin Format.std_formatter 100000;
     Format.printf "%s: %!" line;
     if str_pp then Format.fprintf Format.std_formatter "\"@[%a@]\" %!" (str_pp_obj env sigma) (CoqConstr def_term);
     if de_bruijn then Format.printf "@[%a@] %!" pp (Serlib.Ser_constr.sexp_of_constr def_term);
     Format.printf "@[%a@]@\n%!" pp (Serlib.Ser_glob_term.sexp_of_glob_constr gdef_term)
  | _ -> ()

let check_pending_proofs ~pstate =
  Option.iter (fun _pstate ->
  (* let pfs = Proof_global.get_all_proof_names pstate in *)
  let pfs = [] in
  if not CList.(is_empty pfs) then
    let msg = let open Pp in
      seq [ str "There are pending proofs: "
          ; pfs |> List.rev |> prlist_with_sep pr_comma Names.Id.print; str "."] in
    CErrors.user_err msg
  ) pstate

let close_document ~doc ~pstate =
  let _doc = Stm.join ~doc in
  check_pending_proofs ~pstate

let sername_version = Sertop.Ser_version.ser_git_version

let sername_man =
  [
    `S "DESCRIPTION";
    `P "Experimental Coq name serializer.";
    `S "USAGE";
    `P "To serialize names listed in `names.txt` in module `Funs.mod`:";
    `Pre "sername -Q fs,Funs --require-lib=Funs.mod names.txt";
    `P "See the documentation on the project's webpage for more information."
  ]

let sername_doc = "sername Coq tool"

open Cmdliner

let driver debug printer disallow_sprop async async_workers error_recovery quick coq_path ml_path load_path rload_path require_lib str_pp de_bruijn body in_file omit_loc omit_att omit_env exn_on_opaque =

  (* closures *)
  let pp = Sertop.Sertop_ser.select_printer printer in
  let process = process_line ~pp ~str_pp ~de_bruijn ~body in

  (* initialization *)
  let options = Serlib.Serlib_init.{ omit_loc; omit_att; omit_env; exn_on_opaque } in
  Serlib.Serlib_init.init ~options;

  let allow_sprop = not disallow_sprop in
  let stm_flags =
    { Sertop.Sertop_init.enable_async = async
    ; deep_edits = false
    ; async_workers
    ; error_recovery
    } in

  let dft_ml_path, vo_path =
    Serapi.Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path in
  let ml_load_path = dft_ml_path @ ml_path in
  let vo_load_path = vo_path @ load_path @ rload_path in

  let doc, sid = create_document ~require_lib ~in_file:"file.v" ~stm_flags ~allow_sprop ~quick ~ml_load_path ~vo_load_path ~debug in

  (* main loop *)
  let in_chan = open_in in_file in
  let () = input_doc ~in_chan ~process ~doc ~sid in (* XX *)
  let pstate = match Stm.state_of_id ~doc sid with
    | Stm.Valid (Some { Vernacstate.lemmas; _ }) -> lemmas
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
    let open Sertop.Sertop_arg in
    let term =
      Term.(const driver
            $ debug $ printer $ disallow_sprop $ async $ async_workers $ error_recovery $ quick $ prelude
            $ ml_include_path $ load_path $ rload_path $ require_lib $ str_pp $ de_bruijn $ body $ input_file $ omit_loc $ omit_att $ omit_env $ exn_on_opaque
           ) in
    let info = Cmd.info "sername" ~version:sername_version ~doc:sername_doc ~man:sername_man in
    Cmd.v info term
  in

  try exit (Cmd.eval ~catch:false sername_cmd)
  with exn ->
    let (e, info) = Exninfo.capture exn in
    fatal_exn e info

let _ = main ()
