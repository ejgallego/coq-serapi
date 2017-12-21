(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
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

  (* Initial LoadPath XXX: Use the coq_pkg record? *)
  iload_path   : Mltop.coq_path list;

  (* Libs to require in STM init *)
  require_libs : (string * string option * bool option) list;

  (* Async flags *)
  aopts        : async_flags;

  (* name of the top-level module *)
  top_name     : string;

  (* callback to load cma/cmo files *)
  ml_load      : (string -> unit) option;

  (* Enable Coq Debug mode *)
  debug        : bool;
}

(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)
let coq_init opts =

  let open Names in

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

  (* Initialize logging. *)
  ignore (Feedback.add_feeder opts.fb_handler);

  (**************************************************************************)
  (* Async setup                                                            *)
  (**************************************************************************)

  (* Set async flags; IMPORTANT, this has to happen before STM.init () ! *)
  let stm_options = Option.cata (fun coqtop ->

      let open Stm.AsyncOpts in
      let opts =
        { default_opts with
          async_proofs_mode = APon;
          (* Imitate CoqIDE *)
          async_proofs_full = opts.aopts.async_full;
          async_proofs_never_reopen_branch = not opts.aopts.deep_edits;
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
    ) Stm.AsyncOpts.default_opts opts.aopts.enable_async in

  (**************************************************************************)
  (* Start the STM!!                                                        *)
  (**************************************************************************)
  Stm.init_core ();

  (* Flags.debug := true; *)

  (* We need to declare a toplevel module name. *)
  let sertop_dp = DirPath.make [Id.of_string opts.top_name] in

  (* Return the initial state of the STM *)
  let ndoc = { Stm.doc_type = Stm.Interactive sertop_dp;
               require_libs = opts.require_libs;
               iload_path   = opts.iload_path;
               stm_options;
             } in
  Stm.new_doc ndoc

(******************************************************************************)
(* Coq Prelude Loading Defaults (to be improved)                              *)
(******************************************************************************)

let coq_loadpath_default ~implicit ~coq_path =
  let open Mltop in
  let mk_path prefix = coq_path ^ "/" ^ prefix in
  let mk_lp ~ml ~root ~dir ~implicit =
    { recursive = true;
      path_spec = VoPath {
          unix_path = mk_path dir;
          coq_path  = root;
          has_ml    = ml;
          implicit;
        };
    } in
  (* in 8.8 we can use Libnames.default_* *)
  let coq_root     = Names.(DirPath.make [Id.of_string "Coq"]) in
  let default_root = Names.(DirPath.empty) in
  [mk_lp ~ml:AddRecML ~root:coq_root     ~implicit       ~dir:"plugins";
   mk_lp ~ml:AddNoML  ~root:coq_root     ~implicit       ~dir:"theories";
   mk_lp ~ml:AddRecML ~root:default_root ~implicit:false ~dir:"user-contrib";
  ]
