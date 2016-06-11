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
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Names
open Sexplib

type id          = Names.Id.t
type name        = Names.Name.t
type dirpath     = Names.DirPath.t
type label       = Names.Label.t
type mbid        = Names.MBId.t
type modpath     = Names.ModPath.t
type kername     = Names.KerName.t
type constant    = Names.Constant.t
type mutind      = Names.MutInd.t
type inductive   = Names.inductive
type constructor = Names.constructor
type projection  = Names.Projection.t

(* Aliases *)
type evaluable_global_reference = Names.evaluable_global_reference

type id_set = Names.Id.Set.t

val id_of_sexp : Sexp.t -> Id.t
val sexp_of_id : Id.t -> Sexp.t

val id_set_of_sexp : Sexp.t -> Id.Set.t
val sexp_of_id_set : Id.Set.t -> Sexp.t

val name_of_sexp : Sexp.t -> Name.t
val sexp_of_name : Name.t -> Sexp.t

val dirpath_of_sexp : Sexp.t -> DirPath.t
val sexp_of_dirpath : DirPath.t -> Sexplib.Sexp.t

val label_of_sexp : Sexp.t -> Label.t
val sexp_of_label : Label.t -> Sexp.t

val mbid_of_sexp : Sexp.t -> MBId.t
val sexp_of_mbid : MBId.t -> Sexplib.Sexp.t

val modpath_of_sexp : Sexp.t -> ModPath.t
val sexp_of_modpath : ModPath.t -> Sexp.t

val kername_of_sexp : Sexp.t -> KerName.t
val sexp_of_kername : KerName.t -> Sexp.t

val constant_of_sexp : Sexp.t -> Constant.t
val sexp_of_constant : Constant.t -> Sexp.t

val mutind_of_sexp : Sexp.t -> MutInd.t
val sexp_of_mutind : MutInd.t -> Sexp.t

val inductive_of_sexp : Sexp.t -> inductive
val sexp_of_inductive : inductive -> Sexp.t

val constructor_of_sexp : Sexp.t -> constructor
val sexp_of_constructor : constructor -> Sexp.t

val projection_of_sexp : Sexp.t -> Projection.t
val sexp_of_projection : Projection.t -> Sexp.t

val evaluable_global_reference_of_sexp : Sexp.t -> Names.evaluable_global_reference
val sexp_of_evaluable_global_reference : Names.evaluable_global_reference -> Sexp.t
