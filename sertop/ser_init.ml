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

(* Init options for coq *)
type coq_opts = {

  (* callback to handle async feedback *)
  fb_handler : Feedback.feedback -> unit;
}

let coq_init opts =
  let open Names in

  (* Internal Coq initialization *)
  Lib.init();

  (* Library initialization *)
  Loadpath.add_load_path "." Nameops.default_root_prefix ~implicit:false;

  (* We need to declare a toplevel module name, not sure if this can
     be avoided.  *)
  let ser_name = DirPath.make [Id.of_string "SerTop"] in
  Declaremods.start_library ser_name;

  (* Initialize the STM. *)
  Stm.init();

  (* Initialize logging. *)
  Feedback.set_logger Feedback.feedback_logger;
  Feedback.set_feeder opts.fb_handler;

  (* Miscellaneous tweaks *)
  (* Vernacentries.enable_goal_printing := false; *)
  Vernacentries.qed_display_script   := false;

  (* Return the initial state of the STM *)
  Stm.get_current_state ()
