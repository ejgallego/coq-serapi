(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

open Sexplib.Std
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

module Stdlib = Ser_stdlib
module Names  = Ser_names
module Vmemitcodes = Ser_vmemitcodes

module Map = Ser_cMap.Make(Int.Map)(Ser_int)

module Delayed =
struct

type delayed = {
  del_file : string;
  del_off : int64;
  del_digest : string;
} [@@deriving sexp,yojson,hash,compare]

type 'a node = ToFetch of delayed | Fetched of 'a [@@deriving sexp,yojson,hash,compare]

type 'a t = 'a node Stdlib.ref [@@deriving sexp,yojson,hash,compare]

end

module VmTable =
struct

type t = {
  table_len : int;
  table_dir : Names.DirPath.t;
  table_val : Vmemitcodes.to_patch Map.t;
} [@@deriving sexp,yojson,hash,compare]

type index = Names.DirPath.t * int [@@deriving sexp,yojson,hash,compare]

end

module OP = struct
type t = [%import: Vmlibrary.t]
type _t = {
  local : VmTable.t;
  foreign : VmTable.t Delayed.t Names.DPmap.t;
}
[@@deriving sexp,yojson,hash,compare]
end

module B = SerType.Pierce(OP)
type t = B.t
 [@@deriving sexp,yojson,hash,compare]

module OQ = struct
type t = [%import: Vmlibrary.index]
type _t = VmTable.index [@@deriving sexp,yojson,hash,compare]
end

module C = SerType.Pierce(OQ)
type index = C.t
 [@@deriving sexp,yojson,hash,compare]

type indirect_code = index Vmemitcodes.pbody_code [@@deriving sexp,yojson,hash,compare]
