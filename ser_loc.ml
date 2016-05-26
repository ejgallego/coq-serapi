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

(**********************************************************************)
(* Loc.mli                                                            *)
(**********************************************************************)

open Sexplib.Std

(* Loc: private *)
type loc = [%import: Loc.t]

type _loc = {
  fname        : string; (** filename *)
  line_nb      : int;    (** start line number *)
  bol_pos      : int;    (** position of the beginning of start line *)
  line_nb_last : int;    (** end line number *)
  bol_pos_last : int;    (** position of the beginning of end line *)
  bp           : int;    (** start position *)
  ep           : int;    (** end position *)
} [@@deriving sexp]

let _loc_put loc =
  let s, p1, p2, p3, p4 = Loc.represent loc in
  { fname   = s;
    line_nb = p1;
    bol_pos = p2;
    bp      = p3;
    ep      = p4;
    line_nb_last = p1;
    bol_pos_last = p2;
  }
let _loc_get l = Loc.create l.fname l.line_nb l.bol_pos (l.bp, l.ep)

let sexp_of_loc loc  = sexp_of__loc (_loc_put loc)
let loc_of_sexp sexp = _loc_get (_loc_of_sexp sexp)

type 'a located = [%import: 'a Loc.located
                  [@with t := loc]]
  [@@deriving sexp]
