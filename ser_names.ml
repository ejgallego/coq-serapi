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
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* open Sexplib *)
open Sexplib.Std

(* open Sexplib.Sexp *)
open Names

(************************************************************************)
(* Serialization of Names.mli                                           *)
(************************************************************************)

(* Id: private *)
type id   = [%import: Names.Id.t]

type _id                = Ser_Id of string [@@deriving sexp]
let _id_put  id         = Ser_Id (Id.to_string id)
let _id_get (Ser_Id id) = Id.of_string id

let id_of_sexp sexp = _id_get (_id_of_sexp sexp)
let sexp_of_id id   = sexp_of__id (_id_put id)

(* Name: public *)
type name = [%import: Names.Name.t
                      [@with Id.t := id]]
            [@@deriving sexp]

(* DirPath: private *)
type dirpath = [%import: Names.DirPath.t]

type _dirpath = Ser_DirPath of id list
      [@@deriving sexp]

let _dirpath_put dp                = Ser_DirPath (DirPath.repr dp)
let _dirpath_get (Ser_DirPath dpl) = DirPath.make dpl

let dirpath_of_sexp sexp = _dirpath_get (_dirpath_of_sexp sexp)
let sexp_of_dirpath dp   = sexp_of__dirpath (_dirpath_put dp)

(* Label: private *)
type label = [%import: Names.Label.t]

(* XXX: This will miss the tag *)
let label_of_sexp sexp  = Label.of_id (id_of_sexp sexp)
let sexp_of_label label = sexp_of_id (Label.to_id label)

(* MBid: private *)
type mbid = [%import: Names.MBId.t]

let mbid_of_sexp _x = MBId.make (DirPath.make []) (Id.of_string "")
let sexp_of_mbid _x = Sexplib.Sexp.Atom ""

(* ModPath: public *)
type modpath = [%import: Names.ModPath.t
                         [@with DirPath.t := dirpath;
                                MBId.t    := mbid;
                                Label.t   := label]]
               [@@deriving sexp]

(* KerName: private *)

type kername = [%import: Names.KerName.t]

let kername_of_sexp _x = KerName.make
    (ModPath.MPfile (DirPath.make [])) (DirPath.make []) (Label.make "")
let sexp_of_kername _x = Sexplib.Sexp.Atom ""

(* Constant: private *)
type constant = [%import: Names.Constant.t]

let constant_of_sexp _x = Constant.make
    (KerName.make2 (ModPath.MPfile (DirPath.make [])) (Label.make ""))
    (KerName.make2 (ModPath.MPfile (DirPath.make [])) (Label.make ""))
let sexp_of_constant _x = Sexplib.Sexp.Atom ""

(* MutInd: private *)

type mutind = [%import: Names.MutInd.t]

let mutind_of_sexp _x = Names.MutInd.make
    (KerName.make2 (ModPath.MPfile (DirPath.make [])) (Label.make ""))
    (KerName.make2 (ModPath.MPfile (DirPath.make [])) (Label.make ""))

let sexp_of_mutind _x = Sexplib.Sexp.Atom ""

(* Inductive and constructor = public *)
type inductive   = [%import: Names.inductive
                             [@with MutInd.t := mutind]]
                   [@@deriving sexp]

type constructor = [%import: Names.constructor] [@@deriving sexp]

(* Projection: private *)
type projection = [%import: Names.Projection.t]

let projection_of_sexp _x = Projection.make (
    Constant.make
    (KerName.make2 (ModPath.MPfile (DirPath.make [])) (Label.make ""))
    (KerName.make2 (ModPath.MPfile (DirPath.make [])) (Label.make "")))
    false

let sexp_of_projection _x = Sexplib.Sexp.Atom ""


