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

open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
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

type _t            = Id of string [@@deriving sexp, yojson, hash, compare]
let _t_put  id     = Id (Id.to_string id)
let _t_get (Id id) = Id.of_string_soft id

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t id   = sexp_of__t (_t_put id)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

let hash x = hash__t (_t_put x)
let hash_fold_t st id = hash_fold__t st (_t_put id)

let compare x y = compare__t (_t_put x) (_t_put y)
end

include Self

module Set = Ser_cSet.Make(Names.Id.Set)(Self)
module Map = Ser_cMap.Make(Names.Id.Map)(Self)

end

module Name = struct

(* Name.t: public *)
type t =
  [%import: Names.Name.t]
  [@@deriving sexp,yojson,hash,compare]

end

module DirPath = struct

(* DirPath.t: private *)
type t = [%import: Names.DirPath.t]

type _t = DirPath of Id.t list
      [@@deriving sexp,yojson,hash,compare]

let _t_put dp            = DirPath (DirPath.repr dp)
let _t_get (DirPath dpl) = DirPath.make dpl

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

let hash x = hash__t (_t_put x)
let hash_fold_t st id = hash_fold__t st (_t_put id)

let compare x y = compare__t (_t_put x) (_t_put y)

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

(* let hash x = Id.hash (Label.to_id x) *)
let hash_fold_t st id = Id.hash_fold_t st (Label.to_id id)

let _t_put x = Label.to_id x
let compare x y = Id.compare (_t_put x) (_t_put y)

end

module MBId = struct

(* MBId.t: private *)
type t = [%import: Names.MBId.t]

type _t = Mbid of int * Id.t * DirPath.t
      [@@deriving sexp,yojson,hash,compare]

let _t_put dp              =
  let i, n, dp = MBId.repr dp in Mbid (i,n,dp)
let _t_get (Mbid (i, n, dp)) = Obj.magic (i, n, dp)

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

(* let hash x = hash__t (_t_put x) *)
let hash_fold_t st id = hash_fold__t st (_t_put id)

let compare x y = compare__t (_t_put x) (_t_put y)

end

module ModPath = struct

(* ModPath.t: public *)
type t = [%import: Names.ModPath.t]
         [@@deriving sexp,yojson,hash,compare]

end

module MPmap = Ser_cMap.Make(MPmap)(ModPath)

(* KerName: private *)
module KerName = struct

type t = [%import: Names.KerName.t]

type _t = KerName of ModPath.t * Label.t
      [@@deriving sexp,yojson,hash,compare]

let _t_put kn              =
  let mp, l = KerName.repr kn in KerName (mp,l)
let _kername_get (KerName (mp,l)) = KerName.make mp l

let t_of_sexp sexp = _kername_get (_t_of_sexp sexp)
let sexp_of_t kn   = sexp_of__t (_t_put kn)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _kername_get)
let to_yojson kn   = _t_to_yojson (_t_put kn)

let hash x = hash__t (_t_put x)
let hash_fold_t st id = hash_fold__t st (_t_put id)

let compare x y = compare__t (_t_put x) (_t_put y)

end

module Constant = struct

(* Constant.t: private *)
type t = [%import: Names.Constant.t]

type _t = Constant of ModPath.t * Label.t
      [@@deriving sexp,yojson,hash,compare]

let _t_put cs = let mp, l = Constant.repr2 cs in Constant (mp,l)
let _t_get (Constant (mp,l)) = Constant.make2 mp l

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

let hash x = hash__t (_t_put x)
let hash_fold_t st id = hash_fold__t st (_t_put id)

let compare x y = compare__t (_t_put x) (_t_put y)

end

module Cmap = Ser_cMap.Make(Cmap)(Constant)
module Cmap_env = Ser_cMap.Make(Cmap_env)(Constant)

module MutInd = struct

(* MutInd.t: private *)
type t = [%import: Names.MutInd.t]

type _t = MutInd of ModPath.t * Label.t
      [@@deriving sexp,yojson,hash,compare]

let _t_put cs              =
  let mp, l = MutInd.repr2 cs in MutInd (mp,l)
let _t_get (MutInd (mp,l)) = MutInd.make2 mp l

let t_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_t dp   = sexp_of__t (_t_put dp)

let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let to_yojson level = _t_to_yojson (_t_put level)

(* let hash x = hash__t (_t_put x) *)
let hash_fold_t st id = hash_fold__t st (_t_put id)

let compare x y = compare__t (_t_put x) (_t_put y)

end

module Mindmap = Ser_cMap.Make(Mindmap)(MutInd)
module Mindmap_env = Ser_cMap.Make(Mindmap_env)(MutInd)

type 'a tableKey =
  [%import: 'a Names.tableKey]
  [@@deriving sexp]

type variable =
  [%import: Names.variable]
  [@@deriving sexp,yojson,hash,compare]

(* Inductive and constructor = public *)
module Ind = struct
  type t =
  [%import: Names.Ind.t]
  [@@deriving sexp,yojson,hash,compare]
end

type inductive =
  [%import: Names.inductive]
  [@@deriving sexp,yojson,hash,compare]

module Construct = struct
  type t =
  [%import: Names.Construct.t]
  [@@deriving sexp,yojson,hash,compare]

end
type constructor =
  [%import: Names.constructor]
  [@@deriving sexp,yojson,hash,compare]

(* Projection: private *)
module Projection = struct

  module Repr = struct
    type _t =
      { proj_ind : inductive
      ; proj_npars : int
      ; proj_arg : int
      ; proj_name : Label.t
      } [@@deriving sexp,yojson]

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
  [@@deriving sexp,yojson]

  type t = [%import: Names.Projection.t]

  let t_of_sexp se = Obj.magic (_t_of_sexp se)
  let sexp_of_t dp = sexp_of__t (Obj.magic dp)

  let of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= Obj.magic)
  let to_yojson level = _t_to_yojson (Obj.magic level)
end

module GlobRef = struct

type t = [%import: Names.GlobRef.t]
  [@@deriving sexp,yojson,hash,compare]

end

(* Evaluable global reference: public *)
(* type evaluable_global_reference =
 *   [%import: Names.evaluable_global_reference]
 *   [@@deriving sexp] *)

type lident =
  [%import: Names.lident]
  [@@deriving sexp,yojson,hash,compare]

type lname =
  [%import: Names.lname]
  [@@deriving sexp,yojson,hash,compare]

type lstring =
  [%import: Names.lstring]
  [@@deriving sexp,yojson,hash,compare]
