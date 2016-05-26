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

open Ser_names
open Ser_globnames

(**********************************************************************)
(* Evar_kinds                                                         *)
(**********************************************************************)

(* Private *)
type evar = [%import: Evar.t]

type _evar                    = Ser_Evar of int [@@deriving sexp]
let _evar_put  evar           = Ser_Evar (Evar.repr evar)
let _evar_get (Ser_Evar evar) = Evar.unsafe_of_int evar

let evar_of_sexp sexp = _evar_get (_evar_of_sexp sexp)
let sexp_of_evar evar = sexp_of__evar (_evar_put evar)

type obligation_definition_status =
  [%import: Evar_kinds.obligation_definition_status]
  [@@deriving sexp]

type evar_kinds = [%import: Evar_kinds.t
                  [@with Globnames.global_reference := global_reference;
                         Names.Id.t        := id;
                         Names.Name.t      := name;
                         Names.inductive   := inductive;
                         Constr.existential_key := evar;
                  ]]
    [@@deriving sexp]

