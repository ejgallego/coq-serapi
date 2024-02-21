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

type ax_ctx = (Names.Label.t * Constr.rel_context * Constr.t) list

type t =
  { predicative : bool
  ; type_in_type : bool
  ; vars   : (Names.Id.t * Constr.t) list
  ; axioms : (Printer.axiom * Constr.t * ax_ctx) list
  ; opaque : (Names.Constant.t * Constr.t) list
  ; trans  : (Names.Constant.t * Constr.t) list
  }

val build : Environ.env -> Constr.t Printer.ContextObjectMap.t -> t
val print : Environ.env -> Evd.evar_map -> t -> Pp.t
