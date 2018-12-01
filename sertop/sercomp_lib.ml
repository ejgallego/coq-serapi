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

let coq_err_handler f x =
  try f x
  with exn ->
    let (e, info) = CErrors.push exn in
    let loc = Loc.get_loc info in
    Format.eprintf "Error: @[%a@]@\n%!"
      Pp.pp_with Pp.(pr_opt_no_spc Topfmt.pr_loc loc ++ fnl ()
                     ++ CErrors.(iprint (e, info)));
    exit 1

let create_document ~in_file ~async ~coq_path ~ml_path ~load_path ~rload_path ~omit_loc ~omit_att ~exn_on_opaque ~debug =

  (* serlib initialization *)
  Serlib_init.init ~omit_loc ~omit_att ~exn_on_opaque;

  let open Sertop_init in

  (* coq initialization *)
  coq_init {
    fb_handler   = (fun _ -> ());  (* XXXX *)
    ml_load      = None;
    debug;
  };

  (* document initialization *)
  let iload_path = Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path @ ml_path @ load_path @ rload_path in

  let open Sertop_init in

  let stm_options =
    { enable_async = async;
      async_full   = false;
      deep_edits   = false;
    } in

  let ndoc = { Stm.doc_type = Stm.VoDoc in_file;
               require_libs = ["Coq.Init.Prelude", None, Some true];
               iload_path;
               stm_options  = Sertop_init.process_stm_flags stm_options;
               } in
  Stm.new_doc ndoc

let process_vernac ~mode ~pp ~doc ~st (CAst.{loc;v=vrn} as ast) =
  let open Format in
  let doc, n_st, tip = Stm.add ~doc ~ontop:st false ast in
  if tip <> `NewTip then
    (eprintf "Fatal Error, got no `NewTip`"; exit 1);
  let open Sertop_arg in
  let () = match mode with
    | C_vo    -> ()
    | C_parse -> ()
    | C_stats ->
      Sercomp_stats.do_stats ?loc vrn
    | C_sexp ->
      printf "@[%a@]@\n%!" pp
        (Ser_cAst.sexp_of_t Ser_vernacexpr.sexp_of_vernac_control ast)
  in
  doc, n_st

let fatal_error msg =
  Topfmt.std_logger Feedback.Error msg;
  flush_all ();
  exit 1

let check_pending_proofs () =
  let pfs = Proof_global.get_all_proof_names () in
  if not (CList.is_empty pfs) then
    fatal_error Pp.(
        seq
          [ str "There are pending proofs: "
          ; pfs |> List.rev |> prlist_with_sep pr_comma Names.Id.print
          ; str "."] )

let close_document ~mode ~doc ~in_file =
  let open Sertop_arg in
  match mode with
  | C_parse -> ()
  | C_sexp  -> ()
  | C_stats ->
    Sercomp_stats.print_stats ()
  | C_vo ->
    let _doc = Stm.join ~doc in
    check_pending_proofs ();
    let ldir = Stm.get_ldir ~doc in
    let out_vo = Filename.(remove_extension in_file) ^ ".vo" in
    Library.save_library_to ldir out_vo (Global.opaque_tables ())

(* Command line processing *)
let comp_version = Ser_version.ser_git_version

type compfun
  =  mode:Sertop_arg.comp_mode
  -> pp:(Format.formatter -> Sexplib.Sexp.t -> unit)
  -> in_file:string
  -> doc:Stm.doc
  -> sid:Stateid.t
  -> Stm.doc

open Cmdliner

let driver fn mode debug printer async coq_path ml_path load_path rload_path in_file omit_loc omit_att exn_on_opaque =

  let pp = Sertop_ser.select_printer printer in

  let doc, sid = create_document ~in_file ~async ~coq_path ~ml_path
      ~load_path ~rload_path ~omit_loc ~omit_att ~exn_on_opaque ~debug in

  let doc = fn ~mode ~pp ~in_file ~doc ~sid in
  close_document ~mode ~doc ~in_file

let maincomp ~ext ~name ~desc ~(compfun:compfun) =
  let input_file =
    let doc = "Input " ^ ext ^ " file." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:("FILE"^ext) ~doc)
  in

  let comp_cmd =
    let doc = name ^ " Coq Compiler" in
    let man = [
      `S "DESCRIPTION";
      `P desc;
    ]
    in
    let open Sertop_arg in
    Term.(const (driver compfun)
          $ comp_mode $ debug $ printer $ async $ prelude
          $ ml_include_path $ load_path $ rload_path $ input_file $ omit_loc $ omit_att $ exn_on_opaque
         ),
    Term.info name ~version:comp_version ~doc ~man
  in

  try match Term.eval comp_cmd with
    | `Error _ -> exit 1
    | _        -> exit 0
  with any ->
    let (e, info) = CErrors.push any in
    Format.eprintf "Error: %a@\n%!" Pp.pp_with (CErrors.iprint (e, info));
    exit 1
