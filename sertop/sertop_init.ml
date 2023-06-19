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
(* Copyright 2016-2019 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* Init options for coq *)
type async_flags =
  { enable_async  : string option
  ; deep_edits    : bool
  ; async_workers : int
  ; error_recovery : bool
  }

type coq_opts =

  { fb_handler   : Format.formatter -> Feedback.feedback -> unit
  (* callback to handle async feedback *)

  ; plugin_load      : (string list -> unit) option
  (* callback to load findlib packages *)

  ; debug        : bool
  (* Enable Coq Debug mode *)

  ; set_impredicative_set : bool
  (* Enable -impredicative-set option *)

  ; allow_sprop  : bool
  (* Allow SProp *)
  ; indices_matter : bool

  ; ml_path : string list
  ; vo_path : Loadpath.vo_path list (** From -R and -Q options usually           *)
}

(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)

(* Reference to feedback_handler *)
let fb = ref 0

(* mirroring what's done in Coqinit.init_runtime () *)
let init_runtime opts =

  (* Core Coq initialization *)
  Lib.init();

  (* --impredicative-set option *)
  Global.set_impredicative_set opts.set_impredicative_set;

  Global.set_indices_matter opts.indices_matter;

  (* --allow-sprop in agreement with coq v8.11  *)
  Global.set_allow_sprop opts.allow_sprop;

  (* XXX fixme *)
  Global.set_native_compiler false;

  (* Loadpath is early in the state now *)

  (* This is for defaults, in case we go back to the protocol setting it *)
  (* let dft_ml, dft_vo =
   *   Serapi.Serapi_paths.(coq_loadpath_default ~implicit:true ~coq_path:Coq_config.coqlib)
   * in
   * let ml_load_path = Option.default dft_ml opts.ml_path in
   * let vo_load_path = Option.default dft_vo opts.vo_path in *)

  List.iter Mltop.add_ml_dir opts.ml_path;
  List.iter Loadpath.add_vo_path opts.vo_path;

  ()

let coq_init opts out_fmt =

  if opts.debug then begin
    Printexc.record_backtrace true;
    (* XXX Use CDebug *)
    (* Flags.debug := true; *)
  end;

  let load_plugin = Sertop_loader.plugin_handler opts.plugin_load in

  (* Custom toplevel is used for bytecode-to-js dynlink  *)
  let ser_mltop : Mltop.toplevel = let open Mltop in
    { load_plugin
    ; load_module = Dynlink.loadfile
    (* We ignore all the other operations for now. *)
    ; add_dir = (fun _ -> ())
    ; ml_loop = (fun _ -> ())
    } in
  Mltop.set_top ser_mltop;

  init_runtime opts;

  (**************************************************************************)
  (* Feedback setup                                                         *)
  (**************************************************************************)

  (* Initialize logging. *)
  fb := Feedback.add_feeder (opts.fb_handler out_fmt);

  (**************************************************************************)
  (* Start the STM!!                                                        *)
  (**************************************************************************)
  Stm.init_core ();

  (* End of initialization *)
  ()

let update_fb_handler ~pp_feed out_fmt =
  Feedback.del_feeder !fb;
  fb := Feedback.add_feeder (pp_feed out_fmt)

(******************************************************************************)
(* Async setup                                                                *)
(******************************************************************************)

(* Set async flags; IMPORTANT, this has to happen before STM.init () ! *)
let process_stm_flags opts =
  let stm_opts = Stm.AsyncOpts.default_opts in
  (* Process error resilience *)
  let async_proofs_tac_error_resilience, async_proofs_cmd_error_resilience =
    if opts.error_recovery
    then Stm.AsyncOpts.FAll, true
    else Stm.AsyncOpts.FNone, false
  in
  let stm_opts =
    { stm_opts with
      async_proofs_tac_error_resilience
    ; async_proofs_cmd_error_resilience }
  in
  (* Enable async mode if requested *)
  Option.cata (fun coqtop ->

    let open Stm.AsyncOpts in
    let opts =
      { stm_opts with
        async_proofs_mode = APon
      (* Imitate CoqIDE *)
      ; async_proofs_never_reopen_branch = not opts.deep_edits
      ; async_proofs_n_workers    = opts.async_workers
      ; async_proofs_n_tacworkers = opts.async_workers
      }
    in

    (* async_proofs_worker_priority); *)

    (* Whether to forward Glob output to the IDE. *)
    (* let _dump_opt = "-no-glob" in
     * AsyncTaskQueue.async_proofs_flags_for_workers := []; *)

    (* The -no-glob for workers seems broken recently *)
    AsyncTaskQueue.async_proofs_flags_for_workers := [];

    (* This is not needed as we won't run workers from the cmdline
       "build system" *)
    (* CoqworkmgrApi.(init High); *)

    (* Uh! XXXX *)
    for i = 0 to Array.length Sys.argv - 1 do
      Array.set Sys.argv i "-m"
    done;
    Array.set Sys.argv 0 coqtop;
    opts
  ) stm_opts opts.enable_async
