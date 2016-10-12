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

module Loc   = Ser_loc
module Names = Ser_names

(* qualid: private *)
type qualid = [%import: Libnames.qualid]

type _qualid =
    Ser_Qualid of Names.DirPath.t * Names.Id.t
  [@@deriving sexp]

let _qualid_put qid                   =
  let dp, id = Libnames.repr_qualid qid in Ser_Qualid (dp, id)

let _qualid_get (Ser_Qualid (dp, id)) = Libnames.make_qualid dp id

let qualid_of_sexp sexp = _qualid_get (_qualid_of_sexp sexp)
let sexp_of_qualid qid  = sexp_of__qualid (_qualid_put qid)

(* reference: public *)
type reference = [%import: Libnames.reference]
  [@@deriving sexp]

