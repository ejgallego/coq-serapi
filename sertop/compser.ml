(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ser_vernacexpr
open Sexplib

let process_vernac ~mode pp ~doc st (CAst.{loc;v=vrn} as ast) =
  let open Format in
  let doc, n_st, tip = Stm.add ~doc ~ontop:st false ast in
  if tip <> `NewTip then
    (eprintf "Fatal Error, got no `NewTip`"; exit 1);
  let open Sertop_arg in
  let () = match mode with
    | C_parse -> ()
    | C_stats -> ()
    | C_sexp ->
      printf "@[%a@]@\n @[%a@]@\n%!" Pp.pp_with (Pp.pr_opt Topfmt.pr_loc loc)
        pp (sexp_of_vernac_control vrn);
  in
  doc, n_st

let compser mode debug printer async coq_path ml_path lp1 lp2 in_file omit_loc omit_att exn_on_opaque =

  (* serlib initialization *)
  Serlib_init.init ~omit_loc ~omit_att ~exn_on_opaque;

  let open Sertop_init in

  let in_chan = open_in in_file                          in
  let pp_sexp = Sertop_ser.select_printer printer        in

  let iload_path = coq_loadpath_default ~implicit:true ~coq_path @ ml_path @ lp1 @ lp2 in

  let doc,sid = coq_init {
    fb_handler   = (fun _ -> ());

    aopts        = { enable_async = async;
                     async_full   = false;
                     deep_edits   = false;
                   };
    iload_path;
    require_libs = ["Coq.Init.Prelude", None, Some true];
    top_name     = "CompSer";
    ml_load      = None;
    debug;
  } in

  let stt = ref (doc, sid) in

  try
    while true; do
      let line = input_line in_chan in
      if String.trim line <> "" then begin
        let vs = Sexp.of_string line in
        let vrn = vernac_control_of_sexp vs in
        let ast = CAst.make vrn in
        stt := process_vernac ~mode pp_sexp ~doc:(fst !stt) (snd !stt) ast
      end
    done
  with End_of_file ->
    let _ = Stm.finish ~doc:(fst !stt) in
    close_in in_chan

(* Command line processing *)
let compser_version = Ser_version.ser_git_version

open Cmdliner

let input_file =
  let doc = "Input sexp file." in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FILE.sexp" ~doc)

let sertop_cmd =
  let doc = "CompSer Coq Compiler" in
  let man = [
    `S "DESCRIPTION";
    `P "Experimental Sexp Coq Compiler."
  ]
  in
  let open Sertop_arg in
  Term.(const compser $ comp_mode $ debug $ printer $ async $ prelude $ ml_include_path $ load_path $ rload_path $ input_file $ omit_loc $ omit_att $ exn_on_opaque ),
  Term.info "compser" ~version:compser_version ~doc ~man

let main () =
  try match Term.eval sertop_cmd with
    | `Error _ -> exit 1
    | _        -> exit 0
  with any ->
    let (e, info) = CErrors.push any in
    Format.eprintf "Error: %a@\n%!" Pp.pp_with (CErrors.iprint (e, info));
    exit 1

let _ = main ()
