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

open Ser_loc
open Ser_xml
open Ser_richpp
open Ser_stateid

type level =
  [%import: Feedback.level]
  [@@deriving sexp]

type edit_id =
  [%import: Feedback.edit_id]
  [@@deriving sexp]

type route_id =
  [%import: Feedback.route_id]
  [@@deriving sexp]

type edit_or_state_id =
  [%import: Feedback.edit_or_state_id
  [@with
     Feedback.edit_id := edit_id;
     state_id := stateid;
  ]]
  [@@deriving sexp]

type feedback_content =
  [%import: Feedback.feedback_content
  [@with
     Stateid.t := stateid;
     Loc.t := loc;
     Xml_datatype.xml := xml;
     Richpp.richpp    := richpp;
  ]]
  [@@deriving sexp]

type feedback =
  [%import: Feedback.feedback
  [@with
     Stateid.t := stateid;
     Feedback.route_id := route_id;
  ]]
  [@@deriving sexp]

