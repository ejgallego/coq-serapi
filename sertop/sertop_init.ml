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
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* Init options for coq *)
type async_flags = {
  enable_async : string option;
  async_full   : bool;
  deep_edits   : bool;
}

type coq_opts = {

  (* callback to handle async feedback *)
  fb_handler   : Feedback.feedback -> unit;

  (* callback to load cma/cmo files *)
  ml_load      : (string -> unit) option;

  (* Enable Coq Debug mode *)
  debug        : bool;

}

(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)
let coq_init opts =

  if opts.debug then begin
    Printexc.record_backtrace true;
    Flags.debug := true;
  end;

  (* Custom toplevel is used for bytecode-to-js dynlink  *)
  Option.iter (fun ml_load ->
      let ser_mltop : Mltop.toplevel = let open Mltop in
        {
          load_obj = ml_load;
          (* We ignore all the other operations for now. *)
          use_file = (fun _ -> ());
          add_dir  = (fun _ -> ());
          ml_loop  = (fun _ -> ());
        } in
      Mltop.set_top ser_mltop
    ) opts.ml_load;

  (* Core Coq initialization *)
  Lib.init();
  Global.set_engagement Declarations.PredicativeSet;

  (**************************************************************************)
  (* Feedback setup                                                         *)
  (**************************************************************************)

  (* Initialize logging. *)
  ignore (Feedback.add_feeder opts.fb_handler);

  (**************************************************************************)
  (* Start the STM!!                                                        *)
  (**************************************************************************)
  Stm.init_core ();

  (* End of initialization *)
  ()

(******************************************************************************)
(* Async setup                                                                *)
(******************************************************************************)

(* Set async flags; IMPORTANT, this has to happen before STM.init () ! *)
let process_stm_flags opts = Option.cata (fun coqtop ->

    (* Whether to forward Glob output to the IDE. *)
    let dumpglob = false in

    let dump_opt =
      if dumpglob then begin
        Dumpglob.feedback_glob ();
        "-feedback-glob"
      end else begin
        Dumpglob.noglob ();
        "-no-glob"
      end
    in

    let open Stm.AsyncOpts in
    let opts =
      { default_opts with
        async_proofs_mode = APon;
        (* Imitate CoqIDE *)
        async_proofs_full = opts.async_full;
        async_proofs_never_reopen_branch = not opts.deep_edits;
        async_proofs_n_workers    = 3;
        async_proofs_n_tacworkers = 3;
      } in
    (* async_proofs_worker_priority); *)
    AsyncTaskQueue.async_proofs_flags_for_workers := [dump_opt];
    CoqworkmgrApi.(init High);
    (* Uh! XXXX *)
    for i = 0 to Array.length Sys.argv - 1 do
      Array.set Sys.argv i "-m"
    done;
    Array.set Sys.argv 0 coqtop;
    opts
  ) Stm.AsyncOpts.default_opts opts.enable_async
