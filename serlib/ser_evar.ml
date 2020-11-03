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

open Sexplib.Std
open Ppx_python_runtime
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

(* Private *)
module EBi = struct
  type t = Evar.t
  type _t = Ser_Evar of int [@@deriving sexp,yojson,python,hash,compare]

  let of_t evar = Ser_Evar (Evar.repr evar)
  let to_t (Ser_Evar evar) = Evar.unsafe_of_int evar
end

module Self = SerType.Biject(EBi)
include Self
module Set = Ser_cSet.Make(Evar.Set)(Self)
