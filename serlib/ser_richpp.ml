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

module Xml_datatype = Ser_xml_datatype

type richpp = Richpp.richpp

let richpp_of_sexp sexp = Richpp.richpp_of_xml (Xml_datatype.xml_of_sexp sexp)
let sexp_of_richpp rpp  = Xml_datatype.sexp_of_xml (Richpp.repr rpp)

type located =
  [%import: 'a Richpp.located]
  [@@deriving sexp]
