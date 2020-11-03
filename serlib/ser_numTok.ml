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
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

type sign =
  [%import: NumTok.sign]
  [@@deriving sexp,yojson,python,hash,compare]

type num_class =
  [%import: NumTok.num_class]
  [@@deriving sexp,yojson,python]

type 'a exp =
  [%import: 'a NumTok.exp]
  [@@deriving sexp,yojson,python]

module Unsigned = struct

  module PierceSpec = struct
    type t = NumTok.Unsigned.t
    type _t = {
      int : string;
      frac : string;
      exp : string
    } [@@deriving sexp,yojson,python,hash,compare]
  end

  include SerType.Pierce(PierceSpec)
end

module Signed = struct

  type t =
    [%import: NumTok.Signed.t]
    [@@deriving sexp,yojson,python,hash,compare]

end
