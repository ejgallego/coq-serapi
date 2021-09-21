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

open Sexplib.Std

module Loc       = Ser_loc
module Environ   = Ser_environ
module Reduction = Ser_reduction
module Constr    = Ser_constr
module Evar_kinds = Ser_evar_kinds

type econstr =
  [%import: Evd.econstr]

(* ahhh *)
let econstr_of_sexp s = Obj.magic (Constr.t_of_sexp s)
let sexp_of_econstr c = Constr.sexp_of_t (Obj.magic c)

type evar_body =
  [%import: Evd.evar_body]
  [@@deriving sexp]

module Abstraction = struct

  type abstraction =
    [%import: Evd.Abstraction.abstraction]
    [@@deriving sexp]

  type t =
    [%import: Evd.Abstraction.t]
    [@@deriving sexp]
end

module Filter = struct

  type t = Evd.Filter.t
  let t_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Evd.Filter.t"
  let sexp_of_t = Serlib_base.sexp_of_opaque ~typ:"Evd.Filter.t"

end

module Identity = struct

  type t = Evd.Identity.t
  let t_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Evd.Identity.t"
  let sexp_of_t = Serlib_base.sexp_of_opaque ~typ:"Evd.Identity.t"

end

type evar_info =
  [%import: Evd.evar_info]
  [@@deriving sexp]

type conv_pb = Reduction.conv_pb
  [@@deriving sexp]

type evar_constraint =
  [%import: Evd.evar_constraint]
  [@@deriving sexp]

type unsolvability_explanation =
  [%import: Evd.unsolvability_explanation]
  [@@deriving sexp]
