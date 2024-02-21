(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

val coq_pp_opt : Pp.t -> Pp.t

val feedback_pos_filter : string -> Feedback.feedback -> Feedback.feedback

(* Optimizer/filter for feedback *)
type fb_filter_opts = {
  pp_opt : bool;
}

val default_fb_filter_opts : fb_filter_opts

val feedback_opt_filter : ?opts:fb_filter_opts -> Feedback.feedback -> Feedback.feedback option

val feedback_tr : Feedback.feedback -> Serapi.Serapi_protocol.feedback
