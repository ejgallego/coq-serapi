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

(* We ship our own type due to Context lack of support for anything
   other than Constr.t *)
type 'a hyp = (Names.Id.t list * 'a option * 'a)
type info =
  { evar : Evar.t
  ; name : Names.Id.t option
  }
type 'a reified_goal =
  { info : info
  ; ty   : 'a
  ; hyp  : 'a hyp list
  }

type 'a ser_goals =
  { goals : 'a list
  ; stack : ('a list * 'a list) list
  ; bullet : Pp.t option
  ; shelf : 'a list
  ; given_up : 'a list
  }

(** Stm-independent goal processor *)
val process_goal_gen :
  (Environ.env -> Evd.evar_map -> Constr.t -> 'a)
  -> Evd.evar_map
  -> Evar.t
  -> 'a reified_goal

(* Ready to make into a GADT *)
val get_goals_gen
  :  (Environ.env -> Evd.evar_map -> Constr.t -> 'a)
  -> doc:Stm.doc -> Stateid.t -> 'a reified_goal ser_goals option

val get_goals  : doc:Stm.doc -> Stateid.t -> Constr.t               reified_goal ser_goals option
val get_egoals : doc:Stm.doc -> Stateid.t -> Constrexpr.constr_expr reified_goal ser_goals option
