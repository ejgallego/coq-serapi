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
(* Copyright 2016-2018 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let parse_document ~mode pp ~doc sid in_pa =
  let stt = ref (doc, sid) in
  try while true do
      let east = Stm.parse_sentence ~doc:(fst !stt) (snd !stt) in_pa in
      stt := Complib.process_vernac ~mode ~pp ~doc:(fst !stt) ~st:(snd !stt) east
    done
  with any ->
    let (e, _info) = CErrors.push any in
    match e with
    | Stm.End_of_input -> ()
    | any          ->
      let (e, info) = CErrors.push any in
      Format.eprintf "Error: %a@\n%!" Pp.pp_with (CErrors.iprint (e, info));
      exit 1
    (* Format.eprintf "Error in parsing@\n%!" (\* XXX: add loc *\) *)

let sercomp mode debug printer async coq_path ml_path lp1 lp2 in_file omit_loc omit_att exn_on_opaque =

  (* serlib initialization *)
  Serlib_init.init ~omit_loc ~omit_att ~exn_on_opaque;

  let open Sertop_init in

  (* coq initialization *)
  coq_init {
    (* XXXX *)
    fb_handler   = (fun _ -> ());
    ml_load      = None;
    debug;
  };

  (* document initialization *)
  let iload_path = Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path @ ml_path @ lp1 @ lp2 in
  let doc, sid = Complib.create_from_file ~in_file ~async ~iload_path in

  (* main loop *)

  (* let pp_opt  fb   = Sertop_util.feedback_opt_filter fb                in
   * let pp_feed fb   = Option.iter (fun fb -> pp_answer (SP.Feedback fb)) (pp_opt fb) in *)

  let in_chan = open_in in_file                          in
  let in_strm = Stream.of_channel in_chan                in
  let in_pa   = Pcoq.Parsable.make ~file:(Loc.InFile in_file) in_strm in
  let pp_sexp = Sertop_ser.select_printer printer        in

  parse_document ~mode pp_sexp ~doc sid in_pa;
  close_in in_chan;
  Complib.close_document ~mode

let _ =
  Complib.maincomp ~ext:".v" ~name:"sercomp"
    ~desc:"Experimental Coq Compiler with serialization support."
    ~compfun:sercomp
