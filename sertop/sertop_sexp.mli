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

type ser_opts =
{ in_chan  : in_channel
; out_chan : out_channel         (** Input/Output channels                    *)

; printer  : Sertop_ser.ser_printer
                                 (** Printer type                             *)

; debug    : bool                (** Enable Coq debug mode                    *)
; set_impredicative_set: bool    (** Enable Coq -impredicative-set option *)
; allow_sprop: bool              (** Allow using the proof irrelevant SProp sort *)
; indices_matter : bool          (** Indices of indexes contribute to inductive level *)
; print0   : bool                (** End every answer with [\0]               *)
; lheader  : bool                (** Print lenght header (deprecated)         *)

; no_init  : bool                (** Whether to create the initial document   *)
; no_prelude : bool              (** Whether to load stdlib's prelude         *)
; topfile  : string option       (** Top name is derived from topfile name    *)

(* Coq options *)
; ml_path : string list
; vo_path : Loadpath.vo_path list (** From -R and -Q options usually           *)
; async    : Sertop_init.async_flags
                                 (** Async flags                              *)
}
(** Options for the sertop interactive toplevel                               *)

(******************************************************************************)
(* Input/Output -- Main Loop                                                  *)
(******************************************************************************)

val ser_loop : ser_opts -> unit
(** [ser_loop opts] main se(xp)r-protocol interactive loop *)
