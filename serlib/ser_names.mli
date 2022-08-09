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
  include SerType.SJPHC with type t = Id.t

  module Set : SerType.SJPHC with type t = Id.Set.t
  module Map : SerType.SJPHC1 with type 'a t = 'a Id.Map.t
end

module Name    : SerType.SJPHC with type t = Name.t
module DirPath : SerType.SJPHC with type t = DirPath.t
module DPmap   : Ser_cMap.ExtS with type key = DirPath.t and type 'a t = 'a DPmap.t

module Label   : SerType.SJPHC with type t = Label.t
module MBId    : SerType.SJPHC with type t = MBId.t
module ModPath : SerType.SJPHC with type t = ModPath.t
module MPmap   : Ser_cMap.ExtS with type key = ModPath.t and type 'a t = 'a MPmap.t

module KerName  : SerType.SJPHC with type t = KerName.t
module Constant : SerType.SJPHC with type t = Constant.t

module Cset_env : Ser_cSet.ExtS with type elt = Constant.t and type t = Cset_env.t

module Cmap : Ser_cMap.ExtS with type key = Constant.t and type 'a t = 'a Cmap.t
module Cmap_env : Ser_cMap.ExtS with type key = Constant.t and type 'a t = 'a Cmap_env.t

module MutInd : SerType.SJP with type t = MutInd.t

module Mindmap : Ser_cMap.ExtS with type key = MutInd.t and type 'a t = 'a Mindmap.t
module Mindmap_env : Ser_cMap.ExtS with type key = MutInd.t and type 'a t = 'a Mindmap_env.t

module Indset_env : Ser_cSet.ExtS with type elt = inductive and type t = Indset_env.t

type 'a tableKey = 'a Names.tableKey

val tableKey_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a tableKey
val sexp_of_tableKey : ('a -> Sexp.t) -> 'a tableKey -> Sexp.t

type variable    = Names.variable [@@deriving sexp,yojson,python,hash,compare]
type inductive   = Names.inductive [@@deriving sexp,yojson,python,hash,compare]
type constructor = Names.constructor [@@deriving sexp,yojson,python,hash,compare]

(* -- end modularize -- *)

module Projection : sig

  include SerType.SJPHC with type t = Projection.t

  module Repr : sig
    include SerType.S with type t = Projection.Repr.t
  end

end

module GlobRef : SerType.SJPHC with type t = Names.GlobRef.t

type lident = Names.lident [@@deriving sexp,yojson,python,hash,compare]
type lname = Names.lname [@@deriving sexp,yojson,python,hash,compare]
type lstring = Names.lstring [@@deriving sexp,yojson,python,hash,compare]
