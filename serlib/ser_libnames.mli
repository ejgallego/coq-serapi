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

open Sexplib

type qualid = Libnames.qualid

val qualid_of_sexp : Sexp.t -> Libnames.qualid
val sexp_of_qualid : Libnames.qualid -> Sexp.t
val qualid_of_yojson : Yojson.Safe.t -> (qualid, string) Result.result
val qualid_to_yojson : qualid -> Yojson.Safe.t

type full_path = Libnames.full_path

val full_path_of_sexp : Sexp.t -> Libnames.full_path
val sexp_of_full_path : Libnames.full_path -> Sexp.t
val full_path_of_yojson : Yojson.Safe.t -> (full_path, string) Result.result
val full_path_to_yojson : full_path -> Yojson.Safe.t
