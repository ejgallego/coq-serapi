(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let sertop_dp =
  let open Names in
  DirPath.make [Id.of_string "SerTop"]

(* Init options for coq *)
type async_flags = {
  enable_async : string option;
  async_full   : bool;
  deep_edits   : bool;
}

type coq_opts = {
  (* callback to handle async feedback *)
  fb_handler   : Feedback.feedback -> unit;
  (* Async flags *)
  aopts        : async_flags;
}

let coq_init opts =

  (* Internal Coq initialization *)
  Lib.init();

  Goptions.set_string_option_value ["Default";"Proof";"Mode"] "Classic";

  (* Mltop.init_known_plugins (); *)
  Global.set_engagement Declarations.PredicativeSet;

  (* Library initialization *)
  Loadpath.add_load_path "." Nameops.default_root_prefix ~implicit:false;

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

  (* Set async flags; IMPORTANT, this has to happen before STM.init () ! *)
  Option.iter (fun coqtop ->

      Flags.async_proofs_mode := Flags.APon;
      (* Imitate CoqIDE *)
      Flags.async_proofs_full := opts.aopts.async_full;
      Flags.async_proofs_never_reopen_branch := not opts.aopts.deep_edits;
      Flags.async_proofs_flags_for_workers := [dump_opt];
      Flags.async_proofs_n_workers    := 3;
      Flags.async_proofs_n_tacworkers := 3;
      (* async_proofs_worker_priority); *)
      CoqworkmgrApi.(init Flags.High);
      (* Uh! XXXX *)
      for i = 0 to Array.length Sys.argv - 1 do
        Array.set Sys.argv i "-m"
      done;
      Array.set Sys.argv 0 coqtop
    ) opts.aopts.enable_async;

  (* We need to declare a toplevel module name, not sure if this can
     be avoided.  *)
  Declaremods.start_library sertop_dp;

  (* Initialize the STM. *)
  Stm.init();

  (* Initialize logging. *)
  Feedback.set_logger Feedback.feedback_logger;
  Feedback.set_feeder opts.fb_handler;

  (* Miscellaneous tweaks *)
  Vernacentries.enable_goal_printing := false;
  Vernacentries.qed_display_script   := false;

  (* Flags.debug := true; *)

  (* Return the initial state of the STM *)
  (* Stm.get_current_state () *)
  ()

let coq_init_plugins =
  [ ["syntax"]
  ; ["decl_mode"]
  ; ["cc"]
  ; ["firstorder"]
  ; ["extraction"]
  ; ["funind"]
  ; ["quote"]
  ; ["setoid_ring"]
  ]

let coq_init_theories =
  [ ["Init"]
  ; ["Bool"]
  ; ["Unicode"]

  ; ["Lists"]
  ; ["Vectors"]

  ; ["Logic"]
  ; ["Program"]

  ; ["Classes"]
  ; ["Relations"]
  ; ["Structures"]
  ; ["Setoids"]

  ; ["Numbers"]
  ; ["Numbers"; "NatInt"]
  ; ["Numbers"; "Natural"; "Abstract"]
  ; ["Numbers"; "Natural"; "Peano"]
  ; ["Numbers"; "Integer"; "Abstract"]

  ; ["Arith"]
  ; ["PArith"]
  ; ["NArith"]
  ; ["ZArith"]
  ; ["QArith"]

  ]
