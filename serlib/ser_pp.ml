(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_python_runtime

type pp_tag =
  [%import: Pp.pp_tag]
  [@@deriving sexp, yojson, python]

type block_type =
  [%import: Pp.block_type]
  [@@deriving sexp, yojson, python]

module P = struct
  type _t =
  | Pp_empty
  | Pp_string of string
  | Pp_glue of _t list
  | Pp_box  of block_type * _t
  | Pp_tag  of pp_tag * _t
  (* Are those redundant? *)
  | Pp_print_break of int * int
  | Pp_force_newline
  | Pp_comment of string list
  [@@deriving sexp, yojson, python]

  open Pp

  let rec from_t (d : t) : _t = match repr d with
  | Ppcmd_empty -> Pp_empty
  | Ppcmd_string s -> Pp_string s
  | Ppcmd_glue l -> Pp_glue (List.map from_t l)
  | Ppcmd_box (bt,d) -> Pp_box(bt, from_t d)
  | Ppcmd_tag (t,d) -> Pp_tag(t, from_t d)
  | Ppcmd_print_break (n,m) -> Pp_print_break(n,m)
  | Ppcmd_force_newline -> Pp_force_newline
  | Ppcmd_comment s -> Pp_comment s

  let rec to_t (d : _t) : t = unrepr (match d with
  | Pp_empty -> Ppcmd_empty
  | Pp_string s -> Ppcmd_string s
  | Pp_glue l -> Ppcmd_glue (List.map to_t l)
  | Pp_box (bt,d) -> Ppcmd_box(bt, to_t d)
  | Pp_tag (t,d) -> Ppcmd_tag(t, to_t d)
  | Pp_print_break (n,m) -> Ppcmd_print_break(n,m)
  | Pp_force_newline -> Ppcmd_force_newline
  | Pp_comment s -> Ppcmd_comment s)

end

type t = Pp.t
let t_of_sexp s = P.(to_t (_t_of_sexp s))
let sexp_of_t d = P.(sexp_of__t (from_t d))

let of_yojson json = Ppx_deriving_yojson_runtime.(P.(_t_of_yojson json >|= to_t))
let to_yojson level = P.(_t_to_yojson (from_t level))

let t_of_python s = P.(to_t (_t_of_python s))
let python_of_t d = P.(python_of__t (from_t d))

type doc_view =
  [%import: Pp.doc_view]
  [@@deriving sexp, yojson, python]
