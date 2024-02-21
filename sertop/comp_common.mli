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

val fatal_exn : exn -> Exninfo.info -> 'a

val create_document :
  debug:bool
  -> set_impredicative_set:bool
  -> disallow_sprop:bool
  -> ml_path:string list
  -> load_path:Loadpath.vo_path list
  -> rload_path:Loadpath.vo_path list
  -> quick:bool
  -> in_file:string
  -> indices_matter:bool
  -> omit_loc:bool
  -> omit_att:bool
  -> exn_on_opaque:bool
  -> omit_env:bool
  -> coq_path:string
  -> async:string option
  -> async_workers:int
  -> error_recovery:bool
  -> Stm.doc * Stateid.t
