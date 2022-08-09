(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

type 'a key = 'a CEphemeron.key

module EBiject = struct
  type 'a t = 'a CEphemeron.key

  type 'a _t = 'a [@@deriving sexp,yojson,python,hash,compare]

  let to_t x = CEphemeron.create x
  let of_t x = CEphemeron.get x
end

module B = SerType.Biject1(EBiject)

let sexp_of_key = B.sexp_of_t
let key_of_sexp = B.t_of_sexp
let python_of_key = B.python_of_t
let key_of_python = B.t_of_python
let key_of_yojson = B.of_yojson
let key_to_yojson = B.to_yojson
let hash_fold_key = B.hash_fold_t
let compare_key = B.compare
