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
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_python_runtime

module String = struct
  type t = string
  let t_of_sexp = string_of_sexp
  let sexp_of_t = sexp_of_string
  let of_yojson s = Ok (Yojson.Safe.Util.to_string s)
  let to_yojson s = `String s
  let t_of_python = Py.String.to_string
  let python_of_t = Py.String.of_string
  let hash = Ppx_hash_lib.Std.Hash.Builtin.hash_string
  let hash_fold_t = Ppx_hash_lib.Std.Hash.Builtin.hash_fold_string
  let compare = String.compare
end

module SM = Serlib.Ser_cMap.Make(CString.Map)(String)

type 'a cstring_map = 'a SM.t
  [@@deriving sexp,python]

let from_bindings bl =
  let open CString.Map in
  List.fold_left (fun m (k,v) -> add k v m) empty bl

let cstring_map_of_sexp f s =
  let s_f = Sexplib.Conv.pair_of_sexp string_of_sexp f in
  let bl  = list_of_sexp s_f s                         in
  from_bindings bl

let sexp_of_cstring_map f m =
  let s_f = Sexplib.Conv.sexp_of_pair sexp_of_string f in
  let l   = CString.Map.bindings m                     in
  sexp_of_list s_f l

type treenode =
  [%import: Ltac_plugin.Profile_ltac.treenode
  [@with CString.Map.t   := cstring_map;
         CString.Map.key := string
  ]]
  [@@deriving sexp,python]
