(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)
open Sexplib

module Names      = Ser_names

module Val = struct

  type 'a typ =
    [%import: 'a Geninterp.Val.typ]

  let _typ_of_sexp _ _ = Obj.magic 0
  let sexp_of_typ _ _ = Sexp.Atom "XXX GENINTERP_TYP"

  type t =
    [%import: Geninterp.Val.t]
    [@@deriving sexp_of]

  let t_of_sexp _ = Obj.magic 0
end

module TacStore = struct
  type t = Geninterp.TacStore.t
  let t_of_sexp _ = CErrors.user_err Pp.(str "[GI Store: Cannot deserialize stores.")
  let sexp_of_t _ = Sexplib.Sexp.Atom "[GENINTERP STORE]"
end

type interp_sign =
  [%import: Geninterp.interp_sign]
  [@@deriving sexp]
