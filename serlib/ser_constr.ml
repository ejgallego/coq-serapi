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

open Sexplib.Std
open Ppx_python_runtime
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

let hash_fold_array = hash_fold_array_frozen

module Names   = Ser_names
module Sorts   = Ser_sorts
module Evar    = Ser_evar
module Univ    = Ser_univ
module Context = Ser_context
module Uint63  = Ser_uint63
module Float64 = Ser_float64

type metavariable =
  [%import: Constr.metavariable]
  [@@deriving sexp,yojson,python,hash,compare]

type pconstant =
  [%import: Constr.pconstant]
  [@@deriving sexp,yojson,python,hash,compare]

type pinductive =
  [%import: Constr.pinductive]
  [@@deriving sexp,yojson,python,hash,compare]

type pconstructor =
  [%import: Constr.pconstructor]
  [@@deriving sexp,yojson,python,hash,compare]

type cast_kind =
  [%import: Constr.cast_kind]
  [@@deriving sexp,yojson,python,hash,compare]

type case_style =
  [%import: Constr.case_style]
  [@@deriving sexp,yojson,python,hash,compare]

type case_printing =
  [%import: Constr.case_printing]
  [@@deriving sexp,yojson,python,hash,compare]

type case_info =
  [%import: Constr.case_info]
  [@@deriving sexp,yojson,python,hash,compare]

type 'constr pexistential =
  [%import: 'constr Constr.pexistential]
  [@@deriving sexp,yojson,python,hash,compare]

type ('constr, 'types) prec_declaration =
  [%import: ('constr, 'types) Constr.prec_declaration]
  [@@deriving sexp,yojson,python,hash,compare]

type ('constr, 'types) pfixpoint =
  [%import: ('constr, 'types) Constr.pfixpoint]
  [@@deriving sexp,yojson,python,hash,compare]

type ('constr, 'types) pcofixpoint =
  [%import: ('constr, 'types) Constr.pcofixpoint]
  [@@deriving sexp,yojson,python,hash,compare]

type constr = Constr.constr
type types  = Constr.constr

type 'constr pcase_invert =
  [%import: 'constr Constr.pcase_invert]
  [@@deriving sexp,yojson,python,hash,compare]

let map_pcase_invert f = function
  | NoInvert -> NoInvert
  | CaseInvert { indices } ->
    CaseInvert { indices = Array.map f indices }

type 'constr pcase_branch =
  [%import: 'constr Constr.pcase_branch]
  [@@deriving sexp,yojson,python,hash,compare]

let map_pcase_branch f (bi, c) = (bi, f c)

type 'types pcase_return =
  [%import: 'types Constr.pcase_return]
  [@@deriving sexp,yojson,python,hash,compare]

let map_pcase_return f (bi, c) = (bi, f c)

type _constr =
  | Rel       of int
  | Var       of Names.Id.t
  | Meta      of int
  | Evar      of _constr pexistential
  | Sort      of Sorts.t
  | Cast      of _constr * cast_kind * _constr
  | Prod      of Names.Name.t Context.binder_annot * _constr * _constr
  | Lambda    of Names.Name.t Context.binder_annot * _constr * _constr
  | LetIn     of Names.Name.t Context.binder_annot * _constr * _constr * _constr
  | App       of _constr * _constr array
  | Const     of pconstant
  | Ind       of pinductive
  | Construct of pconstructor
  | Case      of case_info * Univ.Instance.t * _constr array * _constr pcase_return * _constr pcase_invert *  _constr * _constr pcase_branch array
  | Fix       of (_constr, _constr) pfixpoint
  | CoFix     of (_constr, _constr) pcofixpoint
  | Proj      of Names.Projection.t * _constr
  | Int       of Uint63.t
  | Float     of Float64.t
  | Array     of Univ.Instance.t * _constr array * _constr * _constr
[@@deriving sexp,yojson,python,hash,compare]

let rec _constr_put (c : constr) : _constr =
  let cr  = _constr_put           in
  let crl = List.map _constr_put  in
  let cra = Array.map _constr_put in
  let crci = map_pcase_invert _constr_put in
  let crcb = map_pcase_branch _constr_put in
  let crcr = map_pcase_return _constr_put in
  let module C = Constr           in
  match C.kind c with
  | C.Rel i               -> Rel(i)
  | C.Var v               -> Var(v)
  | C.Meta(mv)            -> Meta mv
  | C.Evar(ek, csa)       -> Evar (ek, crl csa)
  | C.Sort(st)            -> Sort (st)
  | C.Cast(cs,k,ty)       -> Cast(cr cs, k, cr ty)
  | C.Prod(n,tya,tyr)     -> Prod(n, cr tya, cr tyr)
  | C.Lambda(n,ab,bd)     -> Lambda(n, cr ab, cr bd)
  | C.LetIn(n,u,ab,bd)    -> LetIn(n, cr u, cr ab, cr bd)
  | C.App(hd, al)         -> App(cr hd, cra al)
  | C.Const p             -> Const p
  | C.Ind(p,q)            -> Ind (p,q)
  | C.Construct(p)        -> Construct (p)
  | C.Case(ci, u, ca, pr, pi, c, pb) ->
    Case(ci, u, cra ca, crcr pr, crci pi, cr c, Array.map crcb pb)
  (* (int array * int) * (Name.t array * 'types array * 'constr array)) *)
  | C.Fix(p,(na,u1,u2))   -> Fix(p, (na, cra u1, cra u2))
  | C.CoFix(p,(na,u1,u2)) -> CoFix(p, (na, cra u1, cra u2))
  | C.Proj(p,c)           -> Proj(p, cr c)
  | C.Int i               -> Int i
  | C.Float i             -> Float i
  | C.Array (u,a,e,t)     -> Array(u, cra a, cr e, cr t)

let rec _constr_get (c : _constr) : constr =
  let cr  = _constr_get           in
  let crl = List.map _constr_get  in
  let cra = Array.map _constr_get in
  let crci = map_pcase_invert _constr_get in
  let crcb = map_pcase_branch _constr_get in
  let crcr = map_pcase_return _constr_get in
  let module C = Constr           in
  match c with
  | Rel i               -> C.mkRel i
  | Var v               -> C.mkVar v
  | Meta(mv)            -> C.mkMeta mv
  | Evar(ek, csa)       -> C.mkEvar (ek, crl csa)
  | Sort(st)            -> C.mkSort (st)
  | Cast(cs,k,ty)       -> C.mkCast(cr cs, k, cr ty)
  | Prod(n,tya,tyr)     -> C.mkProd(n, cr tya, cr tyr)
  | Lambda(n,ab,bd)     -> C.mkLambda(n, cr ab, cr bd)
  | LetIn(n,u,ab,bd)    -> C.mkLetIn(n, cr u, cr ab, cr bd)
  | App(hd, al)         -> C.mkApp(cr hd, cra al)
  | Const p             -> C.mkConstU(p)
  | Ind(p,q)            -> C.mkIndU(p, q)
  | Construct(p)        -> C.mkConstructU(p)
  | Case(ci, u, ca, pr, pi, c, pb) -> C.mkCase (ci, u, cra ca, crcr pr, crci pi, cr c, Array.map crcb pb)
  | Fix (p,(na,u1,u2))  -> C.mkFix(p, (na, cra u1, cra u2))
  | CoFix(p,(na,u1,u2)) -> C.mkCoFix(p, (na, cra u1, cra u2))
  | Proj(p,c)           -> C.mkProj(p, cr c)
  | Int i               -> C.mkInt i
  | Float f             -> C.mkFloat f
  | Array (u,a,e,t)     -> C.mkArray(u, cra a, cr e, cr t)

module ConstrBij = struct

  type t = constr

  type _t = _constr
  [@@deriving sexp,yojson,python,hash,compare]

  let to_t = _constr_get
  let of_t = _constr_put

end

module CC = SerType.Biject(ConstrBij)

(* type constr = CC.t *)
let sexp_of_constr = CC.sexp_of_t
let constr_of_sexp = CC.t_of_sexp
let python_of_constr = CC.python_of_t
let constr_of_python = CC.t_of_python
let constr_of_yojson = CC.of_yojson
let constr_to_yojson = CC.to_yojson
let hash_constr = CC.hash
let hash_fold_constr = CC.hash_fold_t
let compare_constr = CC.compare

let sexp_of_types = CC.sexp_of_t
let types_of_sexp = CC.t_of_sexp
let types_of_python = CC.t_of_python
let python_of_types = CC.python_of_t
let types_of_yojson = CC.of_yojson
let types_to_yojson = CC.to_yojson
let hash_types = CC.hash
let hash_fold_types = CC.hash_fold_t
let compare_types = CC.compare

type t = constr

let t_of_sexp = constr_of_sexp
let sexp_of_t = sexp_of_constr
let t_of_python = CC.t_of_python
let python_of_t = CC.python_of_t
let of_yojson = constr_of_yojson
let to_yojson = constr_to_yojson
let hash = hash_constr
let hash_fold_t = hash_fold_constr
let compare = compare_constr

type case_invert =
  [%import: Constr.case_invert]
  [@@deriving sexp,yojson]


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
  [@@deriving sexp,yojson,python,hash,compare]

type named_context =
  [%import: Constr.named_context]
  [@@deriving sexp,yojson,python,hash,compare]

type rel_declaration =
  [%import: Constr.rel_declaration]
  [@@deriving sexp,yojson,python,hash,compare]

type rel_context =
  [%import: Constr.rel_context]
  [@@deriving sexp,yojson,python,hash,compare]
