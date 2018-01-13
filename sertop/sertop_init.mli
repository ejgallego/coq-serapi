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

type async_flags = {
  enable_async : string option;
  async_full   : bool;
  deep_edits   : bool;
}

type coq_opts = {

  (* callback to handle async feedback *)
  fb_handler   : Feedback.feedback -> unit;

  (* Initial LoadPath XXX: Use the coq_pkg record? *)
  iload_path   : (string list * string * bool) list;

  (* Libs to require prior to STM init *)
  require_libs : (Names.DirPath.t * string * bool option) list;

  (* Whether to enable implicit in the stdlib *)
  implicit_std : bool;

  (* Async flags *)
  aopts        : async_flags;

  (* name of the top-level module *)
  top_name     : string;

  (* callback to load cma/cmo files *)
  ml_load      : (string -> unit) option;

  (* Enable Coq Debug mode *)
  debug        : bool;
}

val coq_init : coq_opts -> Stateid.t
