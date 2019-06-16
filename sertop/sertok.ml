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

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)

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

let rec stream_tok n_tok acc (str,loc_fn) source begin_line begin_char =
  let e = Stream.next str in
  let pre_loc : Loc.t = loc_fn n_tok in
  let loc =
    { pre_loc with
      fname = source;
      line_nb = begin_line;
      line_nb_last = begin_line + pre_loc.line_nb_last - 1;
      bp = begin_char + pre_loc.bp;
      ep = begin_char + pre_loc.ep;
    } in
  let l_tok = CAst.make ~loc e in
  if Tok.(equal e EOI) then
    List.rev acc
  else
    stream_tok (n_tok+1) (l_tok::acc) (str,loc_fn) source begin_line begin_char

exception End_of_input
let input_doc ~pp ~in_file ~in_chan ~doc ~sid =
  let open Format in
  let stt = ref (doc, sid) in
  let in_strm = Stream.of_channel in_chan in
  let source = Loc.InFile in_file in
  let in_pa   = Pcoq.Parsable.make ~loc:(Loc.initial source) in_strm in
  let in_bytes = load_file in_file in
  let st = CLexer.get_lexer_state () in
  try while true do
      let doc, sid = !stt in
      let ast =
        match Stm.parse_sentence ~doc ~entry:Pvernac.main_entry sid in_pa with
        | Some ast -> ast
        | None -> raise End_of_input in
      let begin_line, begin_char, end_char =
	match ast.loc with
	| Some lc -> lc.line_nb, lc.bp, lc.ep
	| None -> raise End_of_input in
      let istr =
	Bytes.sub_string in_bytes begin_char (end_char - begin_char)
      in
      let sstr = Stream.of_string istr in
      try
        let lex = CLexer.Lexer.tok_func sstr in
        let sen = Sertop_ser.Sentence (stream_tok 0 [] lex source begin_line begin_char) in
        CLexer.set_lexer_state st;
        printf "@[%a@]@\n%!" pp (Sertop_ser.sexp_of_sentence sen);
        let doc, n_st, tip = Stm.add ~doc ~ontop:sid false ast in
        if tip <> `NewTip then CErrors.user_err ?loc:ast.loc Pp.(str "fatal, got no `NewTip`");
        stt := doc, n_st
      with exn -> begin
        CLexer.set_lexer_state st;
        raise exn
      end
    done;
      !stt
  with End_of_input -> !stt

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

let sertok_version = Ser_version.ser_git_version

let sertok_man =
  [
    `S "DESCRIPTION";
    `P "Experimental Coq tokenizer.";
    `S "USAGE";
    `P "To serialize `fs/fun.v` with logical path `Funs`:";
    `Pre "sertok -Q fs,Funs fs/fun.v > fs/fun.sexp";
    `P "See the documentation on the project's webpage for more information."
  ]

let sertok_doc = "sertok Coq tokenizer"

open Cmdliner

let driver debug printer async async_workers quick coq_path ml_path load_path rload_path in_file omit_loc omit_att exn_on_opaque =

  (* closures *)
  let pp = Sertop_ser.select_printer printer in

  (* initialization *)
  let options = Serlib.Serlib_init.{ omit_loc; omit_att; exn_on_opaque } in
  Serlib.Serlib_init.init ~options;

  let iload_path = Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path @ ml_path @ load_path @ rload_path in
  let doc, sid = create_document ~in_file ~async ~async_workers ~quick ~iload_path ~debug in

  (* main loop *)
  let in_chan = open_in in_file in
  let doc, _sid = input_doc ~pp ~in_file ~in_chan ~doc ~sid in
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

  let sertok_cmd =
    let open Sertop_arg in
    Term.(const driver
          $ debug $ printer $ async $ async_workers $ quick $ prelude
          $ ml_include_path $ load_path $ rload_path $ input_file $ omit_loc $ omit_att $ exn_on_opaque
         ),
    Term.info "sertok" ~version:sertok_version ~doc:sertok_doc ~man:sertok_man
  in

  try match Term.eval ~catch:false sertok_cmd with
    | `Error _ -> exit 1
    | _        -> exit 0
  with exn ->
    let (e, info) = CErrors.push exn in
    fatal_exn e info

let _ = main ()
