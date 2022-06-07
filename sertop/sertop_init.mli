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

type async_flags =
  { enable_async  : string option
  ; deep_edits    : bool
  ; async_workers : int
  ; error_recovery : bool
  }
(** SerAPI flags for asynchronous processing *)

val process_stm_flags : async_flags -> Stm.AsyncOpts.stm_opt
(** [process_stm_flags flags] transforms SerAPI flags into Coq flags *)

type coq_opts =
  { fb_handler   : Format.formatter -> Feedback.feedback -> unit
  (** callback to handle async feedback *)

  ; plugin_load      : (string list -> unit) option
  (** callback to load findlib plugins  *)

  ; debug        : bool
  (** Enable Coq Debug mode             *)

  ; allow_sprop  : bool
  (** allow using the proof irrelevant SProp sort (default=true) *)

  ; indices_matter : bool
  (** Levels of indices (and nonuniform parameters) contribute to the level of inductives *)

  ; ml_path : string list
  ; vo_path : Loadpath.vo_path list (** From -R and -Q options usually           *)

}

val coq_init : coq_opts -> Format.formatter -> unit
(** [coq_init opts] Initialize Coq. This doesn't create a Proof Document. *)

val update_fb_handler : pp_feed:(Format.formatter -> Feedback.feedback -> unit) -> Format.formatter -> unit
