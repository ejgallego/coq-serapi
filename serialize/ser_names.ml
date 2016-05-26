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

open Sexplib.Std

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

type _mbid = Ser_Mbid of id * dirpath
      [@@deriving sexp]

let _mbid_put dp              =
  let _, n, dp = MBId.repr dp in Ser_Mbid (n,dp)
let _mbid_get (Ser_Mbid (n, dp)) = MBId.make dp n

let mbid_of_sexp sexp = _mbid_get (_mbid_of_sexp sexp)
let sexp_of_mbid dp   = sexp_of__mbid (_mbid_put dp)

(* ModPath: public *)
type modpath = [%import: Names.ModPath.t
                         [@with DirPath.t := dirpath;
                                MBId.t    := mbid;
                                Label.t   := label]]
               [@@deriving sexp]

(* KerName: private *)

type kername = [%import: Names.KerName.t]

type _kername = Ser_Kername of modpath * dirpath * label
      [@@deriving sexp]

let _kername_put kn              =
  let mp, dp, l = KerName.repr kn in Ser_Kername (mp,dp,l)
let _kername_get (Ser_Kername (mp,dp,l)) = KerName.make mp dp l

let kername_of_sexp sexp = _kername_get (_kername_of_sexp sexp)
let sexp_of_kername dp   = sexp_of__kername (_kername_put dp)

(* Constant: private *)
type constant = [%import: Names.Constant.t]

type _constant = Ser_Constant of modpath * dirpath * label
      [@@deriving sexp]

let _constant_put cs              =
  let mp, dp, l = Constant.repr3 cs in Ser_Constant (mp,dp,l)
let _constant_get (Ser_Constant (mp,dp,l)) = Constant.make3 mp dp l

let constant_of_sexp sexp = _constant_get (_constant_of_sexp sexp)
let sexp_of_constant dp   = sexp_of__constant (_constant_put dp)

(* MutInd: private *)

type mutind = [%import: Names.MutInd.t]

type _mutind = Ser_Mutind of modpath * dirpath * label
      [@@deriving sexp]

let _mutind_put cs              =
  let mp, dp, l = MutInd.repr3 cs in Ser_Mutind (mp,dp,l)
let _mutind_get (Ser_Mutind (mp,dp,l)) = MutInd.make3 mp dp l

let mutind_of_sexp sexp = _mutind_get (_mutind_of_sexp sexp)
let sexp_of_mutind dp   = sexp_of__mutind (_mutind_put dp)

(* Inductive and constructor = public *)
type inductive   = [%import: Names.inductive
                             [@with MutInd.t := mutind]]
                   [@@deriving sexp]

type constructor = [%import: Names.constructor] [@@deriving sexp]

(* Projection: private *)
type projection = [%import: Names.Projection.t]

type _projection = Ser_Projection of constant * bool
      [@@deriving sexp]

let _projection_put prj              =
  let cs, uf = Projection.constant prj, Projection.unfolded prj in
  Ser_Projection (cs, uf)
let _projection_get (Ser_Projection (cs,uf)) = Projection.make cs uf

let projection_of_sexp sexp = _projection_get (_projection_of_sexp sexp)
let sexp_of_projection dp   = sexp_of__projection (_projection_put dp)
