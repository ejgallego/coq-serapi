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

let compser mode debug printer async coq_path ml_path lp1 lp2 in_file omit_loc omit_att exn_on_opaque =

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
  let iload_path = Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path @ ml_path @ lp1 @ lp2 in
  let doc, sid = Complib.create_from_file ~in_file ~async ~iload_path in

  (* main loop *)
  let in_chan = open_in in_file                          in
  let pp_sexp = Sertop_ser.select_printer printer        in

  let stt = ref (doc, sid) in
  let () = try
    while true; do
      let line = input_line in_chan in
      if String.trim line <> "" then begin
        let vs = Sexp.of_string line in
        let vrn = vernac_control_of_sexp vs in
        let ast = CAst.make vrn in
        stt := Complib.process_vernac ~mode ~pp:pp_sexp ~doc:(fst !stt) ~st:(snd !stt) ast
      end
    done
  with End_of_file -> ()
  in
  let doc = fst !stt in
  let out_vo = Filename.(remove_extension in_file) ^ ".vo" in
  Complib.close_document ~doc ~mode ~out_vo

let _ =
  Complib.maincomp ~ext:".sexp" ~name:"compser"
    ~desc:"Experimental Coq Compiler with deserialization support."
    ~compfun:compser

