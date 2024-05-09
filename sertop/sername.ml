(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

exception End_of_input

let input_doc ~in_chan ~process ~doc ~sid =
  try while true; do
      let line = input_line in_chan in
      if String.trim line <> "" then process ~doc ~sid line
    done
  with End_of_file -> ()

let str_pp_obj env sigma fmt (obj : Serapi.Serapi_protocol.coq_object) : unit =
  Format.fprintf fmt "%a" Pp.pp_with (Serapi.Serapi_protocol.gen_pp_obj env sigma obj)

let context_of_st m = match m with
  | Stm.Valid (Some { Vernacstate.interp = { lemmas = Some pstate; _ } ; _} ) ->
    Vernacstate.LemmaStack.with_top pstate
      ~f:Declare.Proof.get_current_context
  | _ ->
    let env = Global.env () in Evd.from_env env, env

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
     let gdef_term = Detyping.detype Detyping.Now Names.Id.Set.empty env evd edef_term in
     Format.pp_set_margin Format.std_formatter 100000;
     Format.printf "%s: %!" line;
     if str_pp then Format.fprintf Format.std_formatter "\"@[%a@]\" %!" (str_pp_obj env sigma) (CoqConstr def_term);
     if de_bruijn then Format.printf "@[%a@] %!" pp (Serlib.Ser_constr.sexp_of_constr def_term);
     Format.printf "@[%a@]@\n%!" pp (Serlib.Ser_glob_term.sexp_of_glob_constr gdef_term)
  | _ -> ()

let close_document ~doc ~pstate =
  let _doc = Stm.join ~doc in
  Serapi.Serapi_doc.check_pending_proofs ~pstate

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

(* EJGA: XXX process as regular require at create doc time... *)
let do_require ~doc ~sid ~require_lib ~in_file =
  let sent = Printf.sprintf "Require %s." require_lib in
  let in_strm = Gramlib.Stream.of_string sent in
  let in_pa = Pcoq.Parsable.make ~loc:(Loc.initial (InFile { dirpath = None; file = in_file})) in_strm in
  match Stm.parse_sentence ~doc ~entry:Pvernac.main_entry sid in_pa with
  | Some ast ->
    let doc, sid, tip = Stm.add ~doc ~ontop:sid false ast in
    if tip <> NewAddTip then CErrors.user_err ?loc:ast.loc Pp.(str "fatal, got no `NewTip`");
    doc, sid
  | None -> assert false

open Cmdliner

let driver debug printer set_impredicative_set disallow_sprop async async_workers error_recovery quick coq_path ml_path load_path rload_path require_lib str_pp de_bruijn body in_file omit_loc omit_att omit_env exn_on_opaque indices_matter =

  (* closures *)
  let pp = Sertop.Sertop_ser.select_printer printer in
  let process = process_line ~pp ~str_pp ~de_bruijn ~body in

  (* initialization *)
  let doc, sid = Sertop.Comp_common.create_document
      ~debug ~set_impredicative_set ~disallow_sprop ~ml_path ~load_path ~rload_path ~quick ~in_file ~indices_matter
      ~omit_loc ~omit_att ~exn_on_opaque ~omit_env ~coq_path ~async ~async_workers ~error_recovery in

  let doc, sid = Option.cata (fun require_lib -> do_require ~doc ~sid ~require_lib ~in_file) (doc, sid) require_lib in

  (* main loop *)
  let in_chan = open_in in_file in
  let () = input_doc ~in_chan ~process ~doc ~sid in (* XX *)
  let pstate = match Stm.state_of_id ~doc sid with
    | Stm.Valid (Some { Vernacstate.interp = { lemmas; _ }; _ }) -> lemmas
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
            $ debug $ printer $ set_impredicative_set $ disallow_sprop $ async $ async_workers $ error_recovery $ quick $ prelude
            $ ml_include_path $ load_path $ rload_path $ require_lib $ str_pp $ de_bruijn $ body $ input_file $ omit_loc $ omit_att $ omit_env $ exn_on_opaque
            $ indices_matter
           ) in
    let info = Cmd.info "sername" ~version:sername_version ~doc:sername_doc ~man:sername_man in
    Cmd.v info term
  in

  try exit (Cmd.eval ~catch:false sername_cmd)
  with exn ->
    let (e, info) = Exninfo.capture exn in
    Sertop.Comp_common.fatal_exn e info

let _ = main ()
