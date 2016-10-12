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

module Id : sig

  type t = Id.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

  module Set : sig
    type t = Id.Set.t

    val t_of_sexp : Sexp.t -> t
    val sexp_of_t : t -> Sexp.t
  end

end

module Name : sig

  type t = Name.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module DirPath : sig

  type t = DirPath.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module Label : sig

  type t = Label.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module MBId : sig

  type t = MBId.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module ModPath : sig
  type t = ModPath.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module KerName : sig

  type t = KerName.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module Constant : sig

  type t = Constant.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module MutInd : sig

  type t = Names.MutInd.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

(* mostly deprecated alias *)
type kernel_name = Names.kernel_name
type identifier  = Names.identifier
type variable    = Names.variable
type constant    = Names.constant
type inductive   = Names.inductive
type constructor = Names.constructor
type projection  = Names.Projection.t
type evaluable_global_reference = Names.evaluable_global_reference

val kernel_name_of_sexp : Sexp.t -> kernel_name
val sexp_of_kernel_name : kernel_name -> Sexp.t

val identifier_of_sexp : Sexp.t -> identifier
val sexp_of_identifier : identifier -> Sexp.t

val variable_of_sexp : Sexp.t -> variable
val sexp_of_variable : variable -> Sexp.t

val constant_of_sexp : Sexp.t -> constant
val sexp_of_constant : constant -> Sexp.t

val inductive_of_sexp : Sexp.t -> inductive
val sexp_of_inductive : inductive -> Sexp.t

val constructor_of_sexp : Sexp.t -> constructor
val sexp_of_constructor : constructor -> Sexp.t

val projection_of_sexp : Sexp.t -> projection
val sexp_of_projection : projection -> Sexp.t

val evaluable_global_reference_of_sexp : Sexp.t -> evaluable_global_reference
val sexp_of_evaluable_global_reference : evaluable_global_reference -> Sexp.t
