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
open Ppx_python_runtime_serapi

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

type _t            = Id of string [@@deriving sexp, yojson, python]
let _t_put  id     = Id (Id.to_string id)
let _t_get (Id id) = Id.of_string_soft id

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t id   = sexp_of__t (_t_put id)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

let t_of_python sexp = _t_get (_t_of_python sexp)
let python_of_t id   = python_of__t (_t_put id)

end

include Self

module Set = Ser_cSet.MakeJP(Names.Id.Set)(Self)
module Map = Ser_cMap.MakeJP(Names.Id.Map)(Self)

end

module Name = struct

(* Name.t: public *)
type t =
  [%import: Names.Name.t]
  [@@deriving sexp,yojson,python]

end

module DirPath = struct

(* DirPath.t: private *)
type t = [%import: Names.DirPath.t]

type _t = DirPath of Id.t list
      [@@deriving sexp,yojson,python]

let _t_put dp            = DirPath (DirPath.repr dp)
let _t_get (DirPath dpl) = DirPath.make dpl

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

let t_of_python sexp = _t_get (_t_of_python sexp)
let python_of_t dp   = python_of__t (_t_put dp)

end

module DPmap = Ser_cMap.MakeJP(DPmap)(DirPath)

module Label = struct

(* Label.t: private *)
type t = [%import: Names.Label.t]

(* XXX: This will miss the tag *)
let t_of_sexp sexp  = Label.of_id (Id.t_of_sexp sexp)
let sexp_of_t label = Id.sexp_of_t (Label.to_id label)

let of_yojson json = Ppx_deriving_yojson_runtime.(Id.of_yojson json >|= Label.of_id)
let to_yojson level = Id.to_yojson (Label.to_id level)

let t_of_python python  = Label.of_id (Id.t_of_python python)
let python_of_t label = Id.python_of_t (Label.to_id label)

end

module MBId = struct

(* MBId.t: private *)
type t = [%import: Names.MBId.t]

type _t = Mbid of int * Id.t * DirPath.t
      [@@deriving sexp,yojson,python]

let _t_put dp              =
  let i, n, dp = MBId.repr dp in Mbid (i,n,dp)
let _t_get (Mbid (i, n, dp)) = Obj.magic (i, n, dp)

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

let t_of_python python = _t_get (_t_of_python python)
let python_of_t dp   = python_of__t (_t_put dp)

end

module ModPath = struct

(* ModPath.t: public *)
type t = [%import: Names.ModPath.t]
         [@@deriving sexp,yojson,python]

end

module MPmap = Ser_cMap.MakeJP(MPmap)(ModPath)

(* KerName: private *)
module KerName = struct

type t = [%import: Names.KerName.t]

type _kername = KerName of ModPath.t * Label.t
      [@@deriving sexp,yojson,python]

let _kername_put kn              =
  let mp, l = KerName.repr kn in KerName (mp,l)
let _kername_get (KerName (mp,l)) = KerName.make mp l

let t_of_sexp sexp = _kername_get (_kername_of_sexp sexp)
let sexp_of_t kn   = sexp_of__kername (_kername_put kn)

let of_yojson json = Ppx_deriving_yojson_runtime.(_kername_of_yojson json >|= _kername_get)
let to_yojson kn   = _kername_to_yojson (_kername_put kn)

let t_of_python python = _kername_get (_kername_of_python python)
let python_of_t dp   = python_of__kername (_kername_put dp)

end

module Constant = struct

(* Constant.t: private *)
type t = [%import: Names.Constant.t]

type _t = Constant of ModPath.t * Label.t
      [@@deriving sexp,yojson,python]

let _t_put cs = let mp, l = Constant.repr2 cs in Constant (mp,l)
let _t_get (Constant (mp,l)) = Constant.make2 mp l

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

let t_of_python python = _t_get (_t_of_python python)
let python_of_t dp   = python_of__t (_t_put dp)

end

module Cmap = Ser_cMap.MakeJP(Cmap)(Constant)
module Cmap_env = Ser_cMap.MakeJP(Cmap_env)(Constant)

module MutInd = struct

(* MutInd.t: private *)
type t = [%import: Names.MutInd.t]

type _t = MutInd of ModPath.t * Label.t
      [@@deriving sexp,yojson,python]

let _t_put cs              =
  let mp, l = MutInd.repr2 cs in MutInd (mp,l)
let _t_get (MutInd (mp,l)) = MutInd.make2 mp l

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

let t_of_python python = _t_get (_t_of_python python)
let python_of_t dp   = python_of__t (_t_put dp)

end

module Mindmap = Ser_cMap.MakeJP(Mindmap)(MutInd)
module Mindmap_env = Ser_cMap.MakeJP(Mindmap_env)(MutInd)

type 'a tableKey =
  [%import: 'a Names.tableKey]
  [@@deriving sexp]

type variable =
  [%import: Names.variable]
  [@@deriving sexp,yojson,python]

(* Inductive and constructor = public *)
module Ind = struct
  type t =
  [%import: Names.Ind.t]
  [@@deriving sexp,yojson,python]
end

type inductive =
  [%import: Names.inductive]
  [@@deriving sexp,yojson,python]

module Construct = struct
  type t =
  [%import: Names.Construct.t]
  [@@deriving sexp,yojson,python]

end
type constructor =
  [%import: Names.constructor]
  [@@deriving sexp,yojson,python]

(* Projection: private *)
module Projection = struct

  module Repr = struct
    type _t =
      { proj_ind : inductive
      ; proj_npars : int
      ; proj_arg : int
      ; proj_name : Label.t
      } [@@deriving sexp,yojson,python]

    (* missing from OCaml 4.07 , after, it is [Result.map] *)
    let result_map f = function
      | Ok x -> Ok (f x)
      | Error e -> Error e

    type t = Names.Projection.Repr.t
    let t_of_sexp p = Obj.magic (_t_of_sexp p)
    let sexp_of_t p = sexp_of__t (Obj.magic p)
    let to_yojson p = _t_to_yojson (Obj.magic p)
    let of_yojson p = _t_of_yojson p |> result_map Obj.magic
  end

  type _t = Repr.t * bool
  [@@deriving sexp,yojson,python]

  type t = [%import: Names.Projection.t]

  let t_of_sexp se = Obj.magic (_t_of_sexp se)
  let sexp_of_t dp = sexp_of__t (Obj.magic dp)

  let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= Obj.magic)
  let to_yojson level = _t_to_yojson (Obj.magic level)

  let t_of_python se = Obj.magic (_t_of_python se)
  let python_of_t dp = python_of__t (Obj.magic dp)
end

module GlobRef = struct

type t = [%import: Names.GlobRef.t]
  [@@deriving sexp,yojson,python]

end

(* Evaluable global reference: public *)
(* type evaluable_global_reference =
 *   [%import: Names.evaluable_global_reference]
 *   [@@deriving sexp] *)

type lident =
  [%import: Names.lident]
  [@@deriving sexp,yojson,python]

type lname =
  [%import: Names.lname]
  [@@deriving sexp,yojson,python]

type lstring =
  [%import: Names.lstring]
  [@@deriving sexp,yojson,python]
