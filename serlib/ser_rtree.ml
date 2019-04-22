(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv

type 'a _t =
    Param of int * int
  | Node of 'a * 'a _t array
  | Rec of int * 'a _t array
[@@deriving sexp]

type 'a t = 'a Rtree.t

let sexp_of_t f r = sexp_of__t f (Obj.magic r)
let t_of_sexp f r = Obj.magic (_t_of_sexp f r)
