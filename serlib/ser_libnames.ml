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

(* open Sexplib.Std *)

include Ppx_python_runtime

let cmake = CAst.make

module Loc   = Ser_loc
module CAst  = Ser_cAst
module Names = Ser_names

module QIDBIJ = struct
  type t = Libnames.qualid_r
  type _t =
    | Ser_Qualid of Names.DirPath.t * Names.Id.t
    [@@deriving sexp,yojson,python,hash,compare]

  let of_t qid =
    let (dp, id) = Libnames.repr_qualid (cmake qid) in
    Ser_Qualid (dp, id)
  let to_t (Ser_Qualid (dp, id)) = Libnames.(make_qualid dp id).CAst.v
end

module QID = SerType.Biject(QIDBIJ)

type qualid_r = QID.t
let sexp_of_qualid_r = QID.sexp_of_t
let qualid_r_of_sexp = QID.t_of_sexp
let python_of_qualid_r = QID.python_of_t
let qualid_r_of_python = QID.t_of_python
let qualid_r_of_yojson = QID.of_yojson
let qualid_r_to_yojson = QID.to_yojson
(* let hash_qualid_r = QID.hash *)
let hash_fold_qualid_r = QID.hash_fold_t
let compare_qualid_r = QID.compare

(* qualid: private *)
type qualid =
  [%import: Libnames.qualid]
  [@@deriving sexp,yojson,python,hash,compare]

module FP = struct
  type t = Libnames.full_path
  type _t =
    { dirpath : Names.DirPath.t
    ; basename : Names.Id.t }
  [@@deriving sexp,yojson,python,hash,compare]

  let to_t { dirpath; basename } = Libnames.make_path dirpath basename
  let of_t fp = let dirpath, basename = Libnames.repr_path fp in { dirpath; basename }
end

module F = SerType.Biject(FP)

type full_path = F.t
let sexp_of_full_path = F.sexp_of_t
let full_path_of_sexp = F.t_of_sexp
let python_of_full_path = F.python_of_t
let full_path_of_python = F.t_of_python
let full_path_of_yojson = F.of_yojson
let full_path_to_yojson = F.to_yojson
let hash_full_path = F.hash
let hash_fold_full_path = F.hash_fold_t
let compare_full_path = F.compare
