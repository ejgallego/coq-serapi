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

module NumTok = Ser_numTok

type t =
  [%import: Tok.t]
  [@@deriving sexp,yojson,python]

type 'c p =
  [%import: 'c Tok.p]
  [@@deriving sexp_of]

(** GADTS...  *)
type 'c _p =
  | PKEYWORD of string
  | PPATTERNIDENT of string option
  | PIDENT of string option
  | PFIELD of string option
  | PNUMERAL of NumTok.Unsigned.t option
  | PSTRING of string option
  | PLEFTQMARK
  | PBULLET of string option
  | PQUOTATION of string
  | PEOI
  [@@deriving of_sexp,python]

let p_of_sexp f x = Obj.magic (_p_of_sexp f x)

let p_of_python f x = Obj.magic (_p_of_python f x)
let python_of_p f x = python_of__p f (Obj.magic x)
