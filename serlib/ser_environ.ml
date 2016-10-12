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

module Term = Ser_constr

type env =
  [%import: Environ.env]

let env_of_sexp _env  = Environ.env_of_pre_env Pre_env.empty_env
let sexp_of_env _sexp = Sexp.Atom "Env"

type unsafe_judgment =
  [%import: Environ.unsafe_judgment]
  [@@deriving sexp]

