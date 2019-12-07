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
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Names
open Sexplib

module Id : sig
  include SerType.SJ with type t = Id.t

  module Set : SerType.S with type t = Id.Set.t
  module Map : SerType.S1 with type 'a t = 'a Id.Map.t
end

module Name    : SerType.SJ with type t = Name.t
module DirPath : SerType.SJ with type t = DirPath.t
module DPmap   : Ser_cMap.ExtS with type key = DirPath.t and type 'a t = 'a DPmap.t

module Label   : SerType.S with type t = Label.t
module MBId    : SerType.S with type t = MBId.t
module ModPath : SerType.S with type t = ModPath.t
module MPmap   : Ser_cMap.ExtS with type key = ModPath.t and type 'a t = 'a MPmap.t

module KerName  : SerType.S with type t = KerName.t
module Constant : SerType.SJ with type t = Constant.t

module Cmap : Ser_cMap.ExtS with type key = Constant.t and type 'a t = 'a Cmap.t
module Cmap_env : Ser_cMap.ExtS with type key = Constant.t and type 'a t = 'a Cmap_env.t

module MutInd : SerType.S with type t = MutInd.t

module Mindmap : Ser_cMap.ExtS with type key = MutInd.t and type 'a t = 'a Mindmap.t
module Mindmap_env : Ser_cMap.ExtS with type key = MutInd.t and type 'a t = 'a Mindmap_env.t

type 'a tableKey = 'a Names.tableKey

val tableKey_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a tableKey
val sexp_of_tableKey : ('a -> Sexp.t) -> 'a tableKey -> Sexp.t

type variable    = Names.variable
type inductive   = Names.inductive
type constructor = Names.constructor

module Projection : sig

  include SerType.SJ with type t = Projection.t

  module Repr : sig
    type t =
      { proj_ind : inductive;
        proj_npars : int;
        proj_arg : int;
        proj_name : Label.t; }
  end

end

module GlobRef : SerType.SJ with type t = Names.GlobRef.t

val variable_of_sexp : Sexp.t -> variable
val sexp_of_variable : variable -> Sexp.t

val inductive_of_sexp : Sexp.t -> inductive
val sexp_of_inductive : inductive -> Sexp.t

val inductive_of_yojson : Yojson.Safe.t -> (inductive, string) Result.result
val inductive_to_yojson : inductive -> Yojson.Safe.t

val constructor_of_sexp : Sexp.t -> constructor
val sexp_of_constructor : constructor -> Sexp.t

val constructor_of_yojson : Yojson.Safe.t -> (constructor, string) Result.result
val constructor_to_yojson : constructor -> Yojson.Safe.t

type evaluable_global_reference = Names.evaluable_global_reference
val evaluable_global_reference_of_sexp : Sexp.t -> evaluable_global_reference
val sexp_of_evaluable_global_reference : evaluable_global_reference -> Sexp.t

type lident = Names.lident
val lident_of_sexp : Sexp.t -> lident
val sexp_of_lident : lident -> Sexp.t
val lident_of_yojson : Yojson.Safe.t -> (lident, string) Result.result
val lident_to_yojson : lident -> Yojson.Safe.t

type lname = Names.lname
val lname_of_sexp : Sexp.t -> lname
val sexp_of_lname : lname -> Sexp.t
val lname_of_yojson : Yojson.Safe.t -> (lname, string) Result.result
val lname_to_yojson : lname -> Yojson.Safe.t

type lstring = Names.lstring
val lstring_of_sexp : Sexp.t -> lstring
val sexp_of_lstring : lstring -> Sexp.t
val lstring_of_yojson : Yojson.Safe.t -> (lstring, string) Result.result
val lstring_to_yojson : lstring -> Yojson.Safe.t
