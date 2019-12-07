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

type _t            = Id of string [@@deriving sexp, yojson]
let _t_put  id     = Id (Id.to_string id)
let _t_get (Id id) = Id.of_string_soft id

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t id   = sexp_of__t (_t_put id)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

end

include Self

module Set = Ser_cSet.Make(Names.Id.Set)(Self)
module Map = Ser_cMap.Make(Names.Id.Map)(Self)

end

module Name = struct

(* Name.t: public *)
type t =
  [%import: Names.Name.t]
  [@@deriving sexp,yojson]

end

module DirPath = struct

(* DirPath.t: private *)
type t = [%import: Names.DirPath.t]

type _t = DirPath of Id.t list
      [@@deriving sexp,yojson]

let _t_put dp            = DirPath (DirPath.repr dp)
let _t_get (DirPath dpl) = DirPath.make dpl

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

end

module DPmap = Ser_cMap.Make(DPmap)(DirPath)

module Label = struct

(* Label.t: private *)
type t = [%import: Names.Label.t]

(* XXX: This will miss the tag *)
let t_of_sexp sexp  = Label.of_id (Id.t_of_sexp sexp)
let sexp_of_t label = Id.sexp_of_t (Label.to_id label)

let of_yojson json = Ppx_deriving_yojson_runtime.(Id.of_yojson json >|= Label.of_id)
let to_yojson level = Id.to_yojson (Label.to_id level)

end

module MBId = struct

(* MBId.t: private *)
type t = [%import: Names.MBId.t]

type _t = Mbid of int * Id.t * DirPath.t
      [@@deriving sexp,yojson]

let _t_put dp              =
  let i, n, dp = MBId.repr dp in Mbid (i,n,dp)
let _t_get (Mbid (i, n, dp)) = Obj.magic (i, n, dp)

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

end

module ModPath = struct

(* ModPath.t: public *)
type t = [%import: Names.ModPath.t]
         [@@deriving sexp,yojson]

end

module MPmap = Ser_cMap.Make(MPmap)(ModPath)

(* KerName: private *)
module KerName = struct

type t = [%import: Names.KerName.t]

type _kername = KerName of ModPath.t * Label.t
      [@@deriving sexp]

let _kername_put kn              =
  let mp, l = KerName.repr kn in KerName (mp,l)
let _kername_get (KerName (mp,l)) = KerName.make mp l

let t_of_sexp sexp = _kername_get (_kername_of_sexp sexp)
let sexp_of_t dp   = sexp_of__kername (_kername_put dp)

end

module Constant = struct

(* Constant.t: private *)
type t = [%import: Names.Constant.t]

type _t = Constant of ModPath.t * Label.t
      [@@deriving sexp,yojson]

let _t_put cs = let mp, l = Constant.repr2 cs in Constant (mp,l)
let _t_get (Constant (mp,l)) = Constant.make2 mp l

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

end

module Cmap = Ser_cMap.Make(Cmap)(Constant)
module Cmap_env = Ser_cMap.Make(Cmap_env)(Constant)

module MutInd = struct

(* MutInd.t: private *)
type t = [%import: Names.MutInd.t]

type _t = MutInd of ModPath.t * Label.t
      [@@deriving sexp,yojson]

let _t_put cs              =
  let mp, l = MutInd.repr2 cs in MutInd (mp,l)
let _t_get (MutInd (mp,l)) = MutInd.make2 mp l

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

end

module Mindmap = Ser_cMap.Make(Mindmap)(MutInd)
module Mindmap_env = Ser_cMap.Make(Mindmap_env)(MutInd)

type 'a tableKey =
  [%import: 'a Names.tableKey]
  [@@deriving sexp]

type variable =
  [%import: Names.variable]
  [@@deriving sexp,yojson]

(* Inductive and constructor = public *)
type inductive =
  [%import: Names.inductive]
  [@@deriving sexp,yojson]

type constructor =
  [%import: Names.constructor]
  [@@deriving sexp, yojson]

(* Projection: private *)
module Projection = struct

  module Repr = struct
    type t =
      { proj_ind : inductive;
        proj_npars : int;
        proj_arg : int;
        proj_name : Label.t; }
    [@@deriving sexp,yojson]
  end

  type _t = Repr.t * bool
  [@@deriving sexp,yojson]

  type t = [%import: Names.Projection.t]

  let t_of_sexp se = Obj.magic (_t_of_sexp se)
  let sexp_of_t dp = sexp_of__t (Obj.magic dp)

  let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= Obj.magic)
  let to_yojson level = _t_to_yojson (Obj.magic level)
end

module GlobRef = struct

type t = [%import: Names.GlobRef.t]
  [@@deriving sexp,yojson]

end

(* Evaluable global reference: public *)
type evaluable_global_reference =
  [%import: Names.evaluable_global_reference]
  [@@deriving sexp]

type lident =
  [%import: Names.lident]
  [@@deriving sexp,yojson]

type lname =
  [%import: Names.lname]
  [@@deriving sexp,yojson]

type lstring =
  [%import: Names.lstring]
  [@@deriving sexp,yojson]
