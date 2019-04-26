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
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std

open Names

module Int  = Ser_int
module CAst = Ser_cAst

(************************************************************************)
(* Serialization of Names.mli                                           *)
(************************************************************************)

(* Id.t: private *)
module Id = struct

module Self = struct
type t   = [%import: Names.Id.t]

type _t            = Id of string [@@deriving sexp]
let _t_put  id     = Id (Id.to_string id)
let _t_get (Id id) = Id.of_string_soft id

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t id   = sexp_of__t (_t_put id)
end

include Self

module Set = Ser_cSet.Make(Names.Id.Set)(Self)
module Map = Ser_cMap.Make(Names.Id.Map)(Self)

end

module Name = struct

(* Name.t: public *)
type t =
  [%import: Names.Name.t]
  [@@deriving sexp]

end

module DirPath = struct

(* DirPath.t: private *)
type t = [%import: Names.DirPath.t]

type _dirpath = DirPath of Id.t list
      [@@deriving sexp]

let _dirpath_put dp            = DirPath (DirPath.repr dp)
let _dirpath_get (DirPath dpl) = DirPath.make dpl

let t_of_sexp sexp = _dirpath_get (_dirpath_of_sexp sexp)
let sexp_of_t dp   = sexp_of__dirpath (_dirpath_put dp)

end

module Label = struct

(* Label.t: private *)
type t = [%import: Names.Label.t]

(* XXX: This will miss the tag *)
let t_of_sexp sexp  = Label.of_id (Id.t_of_sexp sexp)
let sexp_of_t label = Id.sexp_of_t (Label.to_id label)

end

module MBId = struct

(* MBId.t: private *)
type t = [%import: Names.MBId.t]

type _mbid = Mbid of Id.t * DirPath.t
      [@@deriving sexp]

let _mbid_put dp              =
  let _, n, dp = MBId.repr dp in Mbid (n,dp)
let _mbid_get (Mbid (n, dp)) = MBId.make dp n

let t_of_sexp sexp = _mbid_get (_mbid_of_sexp sexp)
let sexp_of_t dp   = sexp_of__mbid (_mbid_put dp)

end

module ModPath = struct

(* ModPath.t: public *)
type t = [%import: Names.ModPath.t]
         [@@deriving sexp]

end

module MPmap = Ser_cMap.Make(MPmap)(ModPath)

(* KerName: private *)
module KerName = struct

type t = [%import: Names.KerName.t]

type _kername = Kername of ModPath.t * Label.t
      [@@deriving sexp]

let _kername_put kn              =
  let mp, l = KerName.repr kn in Kername (mp,l)
let _kername_get (Kername (mp,l)) = KerName.make mp l

let t_of_sexp sexp = _kername_get (_kername_of_sexp sexp)
let sexp_of_t dp   = sexp_of__kername (_kername_put dp)

end

module Constant = struct

(* Constant.t: private *)
type t = [%import: Names.Constant.t]

type _constant = Constant of ModPath.t * Label.t
      [@@deriving sexp]

let _constant_put cs              =
  let mp, l = Constant.repr2 cs in Constant (mp,l)
let _constant_get (Constant (mp,l)) = Constant.make2 mp l

let t_of_sexp sexp = _constant_get (_constant_of_sexp sexp)
let sexp_of_t dp   = sexp_of__constant (_constant_put dp)

end

module Cmap = Ser_cMap.Make(Cmap)(Constant)
module Cmap_env = Ser_cMap.Make(Cmap_env)(Constant)

module MutInd = struct

(* MutInd.t: private *)
type t = [%import: Names.MutInd.t]

type _mutind = Mutind of ModPath.t * Label.t
      [@@deriving sexp]

let _mutind_put cs              =
  let mp, l = MutInd.repr2 cs in Mutind (mp,l)
let _mutind_get (Mutind (mp,l)) = MutInd.make2 mp l

let t_of_sexp sexp = _mutind_get (_mutind_of_sexp sexp)
let sexp_of_t dp   = sexp_of__mutind (_mutind_put dp)

end

module Mindmap = Ser_cMap.Make(Mindmap)(MutInd)
module Mindmap_env = Ser_cMap.Make(Mindmap_env)(MutInd)

type 'a tableKey =
  [%import: 'a Names.tableKey]
  [@@deriving sexp]

type variable   = [%import: Names.variable]
                  [@@deriving sexp]

(* Inductive and constructor = public *)
type inductive   = [%import: Names.inductive]
                   [@@deriving sexp]

type constructor = [%import: Names.constructor] [@@deriving sexp]

(* Projection: private *)
module Projection = struct

  module Repr = struct
    type t =
      { proj_ind : inductive;
        proj_npars : int;
        proj_arg : int;
        proj_name : Label.t; }
  end

  type t = [%import: Names.Projection.t]

  type _projection = Projection of Constant.t * bool
  [@@deriving sexp]

  let _projection_put prj              =
    let cs, uf = Projection.constant prj, Projection.unfolded prj in
    Projection (cs, uf)

  (* let _projection_get (Projection (cs,uf)) = Projection.make cs uf *)
  (* let _projection_get _ = Obj.magic 0 *)

  (* let t_of_sexp sexp = _projection_get (_projection_of_sexp sexp) *)
  let t_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Projection.t"
  let sexp_of_t dp = sexp_of__projection (_projection_put dp)

end

module GlobRef = struct

type t = [%import: Names.GlobRef.t]
  [@@deriving sexp]

end

(* Evaluable global reference: public *)
type evaluable_global_reference =
  [%import: Names.evaluable_global_reference]
  [@@deriving sexp]

type lident =
  [%import: Names.lident]
  [@@deriving sexp]

type lname =
  [%import: Names.lname]
  [@@deriving sexp]

type lstring =
  [%import: Names.lstring]
  [@@deriving sexp]
