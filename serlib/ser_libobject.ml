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
(* Copyright 2019-2022 Inria                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_python_runtime

module Names = Ser_names
module Mod_subst = Ser_mod_subst

module CString = struct
  module OP = struct type t = CString.Pred.t let name = "CString.Pred.t" end
  module Pred = SerType.Opaque(OP)
end

module OPP = struct
  type t = Libobject.open_filter
  type _t =
    | Unfiltered
    | Filtered of CString.Pred.t
  [@@deriving sexp,yojson,python,hash,compare]
end

module OF = SerType.Pierce(OPP)
type open_filter = OF.t
let open_filter_of_sexp = OF.t_of_sexp
let sexp_of_open_filter = OF.sexp_of_t
let open_filter_of_python = OF.t_of_python
let python_of_open_filter = OF.python_of_t

module Dyn = struct

  type t = Libobject.Dyn.t

  module Reified = struct

    type t =
      (* | Constant of Internal.Constant.t
       * | Inductive of DeclareInd.Internal.inductive_obj *)
      | TaggedAnon of string
    [@@deriving sexp,python]

    let to_t (x : Libobject.Dyn.t) =
      let Libobject.Dyn.Dyn (tag, _) = x in
      TaggedAnon (Libobject.Dyn.repr tag)
  end

  let t_of_sexp x = Serlib_base.opaque_of_sexp ~typ:"Libobject.Dyn.t" x
  let sexp_of_t x = Reified.sexp_of_t (Reified.to_t x)
  let t_of_python x = Serlib_base.opaque_of_python ~typ:"Libobject.Dyn.t" x
  let python_of_t x = Reified.python_of_t (Reified.to_t x)
end

type obj =
  [%import: Libobject.obj]
  [@@deriving sexp,python]

type algebraic_objects =
  [%import: Libobject.algebraic_objects]
and t = [%import: Libobject.t]
and substitutive_objects = [%import: Libobject.substitutive_objects]
[@@deriving sexp,python]
