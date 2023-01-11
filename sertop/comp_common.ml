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
(* Coq's serialization API                                              *)
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Copyright 2019-2022 Inria -- Dual License LGPL 2.1 / GPL3+           *)
(* Written by: Emilio J. Gallego Arias, Karl Palmskog                   *)
(************************************************************************)

let fatal_exn exn info =
  let loc = Loc.get_loc info in
  let msg = Pp.(pr_opt_no_spc Loc.pr loc ++ fnl ()
                ++ CErrors.iprint (exn, info)) in
  Format.eprintf "Error: @[%a@]@\n%!" Pp.pp_with msg;
  exit 1

let create_document ~debug ~set_impredicative_set ~disallow_sprop ~ml_path ~load_path ~rload_path ~quick ~in_file ~indices_matter
  ~omit_loc ~omit_att ~exn_on_opaque ~omit_env ~coq_path ~async ~async_workers ~error_recovery =

  (* initialization *)
  let options = Serlib.Serlib_init.{ omit_loc; omit_att; exn_on_opaque; omit_env } in
  Serlib.Serlib_init.init ~options;

  let dft_ml_path, vo_path =
    Serapi.Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path in
  let ml_path = dft_ml_path @ ml_path in
  let vo_path = vo_path @ load_path @ rload_path in

  let allow_sprop = not disallow_sprop in
  let stm_flags =
    { Sertop_init.enable_async  = async
    ; deep_edits    = false
    ; async_workers = async_workers
    ; error_recovery
    } in

  let open Sertop_init in

  (* coq initialization *)
  coq_init
    { fb_handler = (fun _ _ -> ())  (* XXXX *)
    ; plugin_load = None
    ; debug
    ; set_impredicative_set
    ; allow_sprop
    ; indices_matter
    ; ml_path
    ; vo_path
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

  let injections = [Coqargs.RequireInjection ("Coq.Init.Prelude", None, Some Lib.Import)] in
  Stm.init_process stm_options;
  let ndoc = { Stm.doc_type = Stm.VoDoc in_file
             ; injections
             } in

  (* Workaround, see
     https://github.com/ejgallego/coq-serapi/pull/101 *)
  if quick || stm_flags.enable_async <> None
  then Safe_typing.allow_delayed_constants := true;

  Stm.new_doc ndoc
