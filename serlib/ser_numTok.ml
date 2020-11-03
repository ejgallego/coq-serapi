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
open Ppx_python_runtime_serapi

type sign =
  [%import: NumTok.sign]
  [@@deriving sexp,yojson,python]

type num_class =
  [%import: NumTok.num_class]
  [@@deriving sexp,yojson,python]

type 'a exp =
  [%import: 'a NumTok.exp]
  [@@deriving sexp,yojson,python]

module Unsigned = struct

  type _t = {
    int : string;
    frac : string;
    exp : string
  } [@@deriving sexp,yojson,python]

  type t = NumTok.Unsigned.t
  let t_of_sexp s = Obj.magic (_t_of_sexp s)
  let sexp_of_t s = sexp_of__t (Obj.magic s)
  let of_yojson s = Obj.magic (_t_of_yojson s)
  let to_yojson s = _t_to_yojson (Obj.magic s)
  let t_of_python s = Obj.magic (_t_of_python s)
  let python_of_t s = python_of__t (Obj.magic s)

end

module Signed = struct

  type t =
    [%import: NumTok.Signed.t]
    [@@deriving sexp,yojson,python]

end
