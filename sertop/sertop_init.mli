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
  (* Initial LoadPath XXX: Use a record *)
  iload_path   : (string list * string * bool) list;

  (* Whether to load the prelude non qualified *)
  implicit_prelude : bool;
}

val coq_init : coq_opts -> unit

val coq_init_plugins  : string list list
val coq_init_theories : string list list

val sertop_dp : Names.DirPath.t
