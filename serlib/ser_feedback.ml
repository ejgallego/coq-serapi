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

module Loc = Ser_loc

module Xml_datatype = Ser_xml_datatype
module Pp           = Ser_pp
module Stateid      = Ser_stateid

type level =
  [%import: Feedback.level]
  [@@deriving sexp, yojson, python]

type route_id =
  [%import: Feedback.route_id]
  [@@deriving sexp, yojson, python]

type doc_id =
  [%import: Feedback.doc_id]
  [@@deriving sexp, yojson, python]

type feedback_content =
  [%import: Feedback.feedback_content]
  [@@deriving sexp, yojson]

type feedback =
  [%import: Feedback.feedback]
  [@@deriving sexp, yojson]

