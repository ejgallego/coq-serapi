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
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* Example of serialization to a sexp:

   Coq's main datatype, constr, is a private type so we need to define
   a serializable clone. Unfortunately, its main view is "zippy" so we
   need to recurse throu the constr to build the clone.
*)

open Sexplib
open Sexplib.Std

module Names   = Ser_names
module Sorts   = Ser_sorts
module Evar    = Ser_evar
module Univ    = Ser_univ
module Context = Ser_context
module Uint63  = Ser_uint63
module Float64 = Ser_float64

type metavariable =
  [%import: Constr.metavariable]
  [@@deriving sexp, yojson]

type pconstant =
  [%import: Constr.pconstant]
  [@@deriving sexp, yojson]

type pinductive =
  [%import: Constr.pinductive]
  [@@deriving sexp, yojson]

type pconstructor =
  [%import: Constr.pconstructor]
  [@@deriving sexp, yojson]

type cast_kind =
  [%import: Constr.cast_kind]
  [@@deriving sexp,yojson]

type case_style =
  [%import: Constr.case_style]
  [@@deriving sexp,yojson]

type case_printing =
  [%import: Constr.case_printing]
  [@@deriving sexp,yojson]

type case_info =
  [%import: Constr.case_info]
  [@@deriving sexp,yojson]

type 'constr pexistential =
  [%import: 'constr Constr.pexistential]
  [@@deriving sexp,yojson]

type ('constr, 'types) prec_declaration =
  [%import: ('constr, 'types) Constr.prec_declaration]
  [@@deriving sexp,yojson]

type ('constr, 'types) pfixpoint =
  [%import: ('constr, 'types) Constr.pfixpoint]
  [@@deriving sexp,yojson]

type ('constr, 'types) pcofixpoint =
  [%import: ('constr, 'types) Constr.pcofixpoint]
  [@@deriving sexp,yojson]

type constr = Constr.constr
type types  = Constr.constr

type _constr =
  | Rel       of int
  | Var       of Names.Id.t
  | Meta      of int
  | Evar      of _constr pexistential
  | Sort      of Sorts.t
  | Cast      of _constr * cast_kind * _types
  | Prod      of Names.Name.t Context.binder_annot * _types * _types
  | Lambda    of Names.Name.t Context.binder_annot * _types * _constr
  | LetIn     of Names.Name.t Context.binder_annot * _constr * _types * _constr
  | App       of _constr * _constr array
  | Const     of pconstant
  | Ind       of pinductive
  | Construct of pconstructor
  | Case      of case_info * _constr * _constr * _constr array
  | Fix       of (_constr, _types) pfixpoint
  | CoFix     of (_constr, _types) pcofixpoint
  | Proj      of Names.Projection.t * _constr
  | Int       of Uint63.t
  | Float     of Float64.t
[@@deriving sexp,yojson]
and _types = _constr
[@@deriving sexp,yojson]

let rec _constr_put (c : constr) : _constr =
  let cr  = _constr_put           in
  let cra = Array.map _constr_put in
  let module C = Constr           in
  match C.kind c with
  | C.Rel i               -> Rel(i)
  | C.Var v               -> Var(v)
  | C.Meta(mv)            -> Meta mv
  | C.Evar(ek, csa)       -> Evar (ek, cra csa)
  | C.Sort(st)            -> Sort (st)
  | C.Cast(cs,k,ty)       -> Cast(cr cs, k, cr ty)
  | C.Prod(n,tya,tyr)     -> Prod(n, cr tya, cr tyr)
  | C.Lambda(n,ab,bd)     -> Lambda(n, cr ab, cr bd)
  | C.LetIn(n,u,ab,bd)    -> LetIn(n, cr u, cr ab, cr bd)
  | C.App(hd, al)         -> App(cr hd, cra al)
  | C.Const p             -> Const p
  | C.Ind(p,q)            -> Ind (p,q)
  | C.Construct(p)        -> Construct (p)
  | C.Case(ci, d, c, ca)  -> Case(ci, cr d, cr c, cra ca)
  (* (int array * int) * (Name.t array * 'types array * 'constr array)) *)
  | C.Fix(p,(na,u1,u2))   -> Fix(p, (na, cra u1, cra u2))
  | C.CoFix(p,(na,u1,u2)) -> CoFix(p, (na, cra u1, cra u2))
  | C.Proj(p,c)           -> Proj(p, cr c)
  | C.Int i               -> Int i
  | C.Float i             -> Float i

let rec _constr_get (c : _constr) : constr =
  let cr  = _constr_get           in
  let cra = Array.map _constr_get in
  let module C = Constr           in
  match c with
  | Rel i               -> C.mkRel i
  | Var v               -> C.mkVar v
  | Meta(mv)            -> C.mkMeta mv
  | Evar(ek, csa)       -> C.mkEvar (ek, cra csa)
  | Sort(st)            -> C.mkSort (st)
  | Cast(cs,k,ty)       -> C.mkCast(cr cs, k, cr ty)
  | Prod(n,tya,tyr)     -> C.mkProd(n, cr tya, cr tyr)
  | Lambda(n,ab,bd)     -> C.mkLambda(n, cr ab, cr bd)
  | LetIn(n,u,ab,bd)    -> C.mkLetIn(n, cr u, cr ab, cr bd)
  | App(hd, al)         -> C.mkApp(cr hd, cra al)
  | Const p             -> C.mkConstU(p)
  | Ind(p,q)            -> C.mkIndU(p, q)
  | Construct(p)        -> C.mkConstructU(p)
  | Case(ci, d, c, ca)  -> C.mkCase(ci, cr d, cr c, cra ca)
  | Fix (p,(na,u1,u2))  -> C.mkFix(p, (na, cra u1, cra u2))
  | CoFix(p,(na,u1,u2)) -> C.mkCoFix(p, (na, cra u1, cra u2))
  | Proj(p,c)           -> C.mkProj(p, cr c)
  | Int i               -> C.mkInt i
  | Float f             -> C.mkFloat f

let constr_of_sexp (c : Sexp.t) : constr =
  _constr_get (_constr_of_sexp c)

let sexp_of_constr (c : constr) : Sexp.t =
  sexp_of__constr (_constr_put c)

let constr_of_yojson json = Ppx_deriving_yojson_runtime.(_constr_of_yojson json >|= _constr_get)
let constr_to_yojson level = _constr_to_yojson (_constr_put level)

let types_of_sexp = constr_of_sexp
let sexp_of_types = sexp_of_constr

let types_of_yojson = constr_of_yojson
let types_to_yojson = constr_to_yojson

type t = constr

let t_of_sexp = constr_of_sexp
let sexp_of_t = sexp_of_constr

let of_yojson = constr_of_yojson
let to_yojson = constr_to_yojson

type rec_declaration =
  [%import: Constr.rec_declaration]
  [@@deriving sexp]

type fixpoint =
  [%import: Constr.fixpoint]
  [@@deriving sexp]

type cofixpoint =
  [%import: Constr.cofixpoint]
  [@@deriving sexp]

type existential =
  [%import: Constr.existential]
  [@@deriving sexp]

type sorts_family = Sorts.family
let sorts_family_of_sexp = Sorts.family_of_sexp
let sexp_of_sorts_family = Sorts.sexp_of_family

type named_declaration =
  [%import: Constr.named_declaration]
  [@@deriving sexp]

type named_context =
  [%import: Constr.named_context]
  [@@deriving sexp]

type rel_declaration =
  [%import: Constr.rel_declaration]
  [@@deriving sexp]

type rel_context =
  [%import: Constr.rel_context]
  [@@deriving sexp]
