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

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)

let rec stream_tok n_tok acc str source begin_line begin_char =
  let e = Gramlib.LStream.next (Pcoq.get_keyword_state()) str in
  let pre_loc : Loc.t = Gramlib.LStream.get_loc n_tok str in
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
    stream_tok (n_tok+1) (l_tok::acc) str source begin_line begin_char

exception End_of_input

let input_doc ~pp ~in_file ~in_chan ~doc ~sid =
  let open Format in
  let stt = ref (doc, sid) in
  let in_strm = Serapi.Ser_stream.of_channel in_chan in
  let source = Loc.InFile { dirpath = None; file = in_file } in
  let in_pa   = Pcoq.Parsable.make ~loc:(Loc.initial source) in_strm in
  let in_bytes = load_file in_file in
  try while true do
      let l_pre_st = CLexer.Lexer.State.get () in
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
      let l_post_st = CLexer.Lexer.State.get () in
      let sstr = Serapi.Ser_stream.of_string istr in
      try
	CLexer.Lexer.State.set l_pre_st;
        let lex = CLexer.Lexer.tok_func sstr in
        let sen = Sertop.Sertop_ser.Sentence (stream_tok 0 [] lex source begin_line begin_char) in
        CLexer.Lexer.State.set l_post_st;
        printf "@[%a@]@\n%!" pp (Sertop.Sertop_ser.sexp_of_sentence sen);
        let doc, n_st, tip = Stm.add ~doc ~ontop:sid false ast in
        if tip <> NewAddTip then CErrors.user_err ?loc:ast.loc Pp.(str "fatal, got no `NewTip`");
        stt := doc, n_st
      with exn -> begin
        CLexer.Lexer.State.set l_post_st;
        raise exn
      end
    done;
      !stt
  with End_of_input -> !stt

let close_document ~doc ~pstate =
  let _doc = Stm.join ~doc in
  Serapi.Serapi_doc.check_pending_proofs ~pstate

let sertok_version = Sertop.Ser_version.ser_git_version

let sertok_man =
  [
    `S "DESCRIPTION";
    `P "Experimental Coq tokenizer.";
    `S "USAGE";
    `P "To serialize tokens in the file `fs/fun.v` with logical path `Funs`:";
    `Pre "sertok -Q fs,Funs fs/fun.v > fs/fun.sexp";
    `P "See the documentation on the project's website for more information."
  ]

let sertok_doc = "sertok Coq tokenizer"

open Cmdliner

let driver debug set_impredicative_set disallow_sprop printer async async_workers error_recovery quick coq_path ml_path load_path rload_path in_file omit_loc omit_att omit_env exn_on_opaque indices_matter =

  (* closures *)
  let pp = Sertop.Sertop_ser.select_printer printer in

  (* initialization *)
  let doc, sid = Sertop.Comp_common.create_document
      ~debug ~set_impredicative_set ~disallow_sprop ~ml_path ~load_path ~rload_path ~quick ~in_file ~indices_matter
      ~omit_loc ~omit_att ~exn_on_opaque ~omit_env ~coq_path ~async ~async_workers ~error_recovery in

  (* main loop *)
  let in_chan = open_in in_file in
  let doc, _sid = input_doc ~pp ~in_file ~in_chan ~doc ~sid in
  let pstate = match Stm.state_of_id ~doc sid with
    | Valid (Some { Vernacstate.interp = { lemmas; _ }; _ }) -> lemmas
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
    let open Sertop.Sertop_arg in
    let term =
      Term.(const driver
            $ debug $ set_impredicative_set $ disallow_sprop $ printer $ async $ async_workers $ error_recovery $ quick $ prelude
            $ ml_include_path $ load_path $ rload_path $ input_file $ omit_loc $ omit_att $ omit_env $ exn_on_opaque
            $ indices_matter
           ) in
    let info = Cmd.info "sertok" ~version:sertok_version ~doc:sertok_doc ~man:sertok_man in
    Cmd.v info term
  in

  try
    let ecode = Cmd.eval ~catch:false sertok_cmd in
    exit ecode
  with exn ->
    let (e, info) = Exninfo.capture exn in
    Sertop.Comp_common.fatal_exn e info

let _ = main ()
