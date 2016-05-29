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

(* Example of serialization to a sexp:

   Coq's main datatype, constr, is a private type so we need to define
   a serializable clone. Unfortunately, its main view is "zippy" so we
   need to recurse throu the constr to build the clone.
*)

open Sexplib
open Sexplib.Std

open Ser_names
open Ser_sorts
open Ser_evar
open Ser_univ

(* type 'a puniverses = *)
(*   [%import: 'a Constr.puniverses *)
(*   [@with *)
(*      Univ.puniverses := puniverses; *)
(*   ]] *)
(*   [@@deriving sexp] *)

type pconstant =
  [%import: Constr.pconstant
  [@with
     Names.constant := constant;
  ]]
  [@@deriving sexp]

type pinductive =
  [%import: Constr.pinductive
  [@with
     Names.inductive := inductive;
  ]]
  [@@deriving sexp]

type pconstructor =
  [%import: Constr.pconstructor
  [@with
     Names.constructor := constructor;
  ]]
  [@@deriving sexp]

type existential_key =
  [%import: Constr.existential_key
  [@with
    Evar.t := evar;
  ]]
  [@@deriving sexp]

type cast_kind =
  [%import: Constr.cast_kind]
  [@@deriving sexp]

type case_style =
  [%import: Constr.case_style]
  [@@deriving sexp]

type case_printing =
  [%import: Constr.case_printing]
  [@@deriving sexp]

type case_info =
  [%import: Constr.case_info
  [@with
     Names.inductive := inductive;
  ]]
  [@@deriving sexp]

type 'constr pexistential =
  [%import: 'constr Constr.pexistential]
  [@@deriving sexp]

type ('constr, 'types) prec_declaration =
  [%import: ('constr, 'types) Constr.prec_declaration
  [@with
    Names.Name.t := name;
  ]]
  [@@deriving sexp]

type ('constr, 'types) pfixpoint =
  [%import: ('constr, 'types) Constr.pfixpoint]
  [@@deriving sexp]

type ('constr, 'types) pcofixpoint =
  [%import: ('constr, 'types) Constr.pcofixpoint]
  [@@deriving sexp]

type constr =
  | Rel       of int
  | Var       of id
  | Meta      of int
  | Evar      of constr pexistential
  | Sort      of sort
  | Cast      of constr * cast_kind * types
  | Prod      of name * types * types
  | Lambda    of name * types * constr
  | LetIn     of name * constr * types * constr
  | App       of constr * constr array
  | Const     of pconstant
  | Ind       of pinductive
  | Construct of pconstructor
  | Case      of case_info * constr * constr * constr array
  | Fix       of (constr, types) pfixpoint
  | CoFix     of (constr, types) pcofixpoint
  | Proj      of projection * constr
and types = constr
[@@deriving sexp]

let rec _constr_put (c : Constr.constr) : constr =
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

let rec _constr_get (c : constr) : Constr.constr =
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
  | Const p             -> C.mkConst (fst p)
  | Ind(p,_q)           -> C.mkInd (fst p, snd p)
  | Construct(p)        -> C.mkConstruct (fst p)
  | Case(ci, d, c, ca)  -> C.mkCase(ci, cr d, cr c, cra ca)
  | Fix (p,(na,u1,u2))  -> C.mkFix(p, (na, cra u1, cra u2))
  | CoFix(p,(na,u1,u2)) -> C.mkCoFix(p, (na, cra u1, cra u2))
  | Proj(p,c)           -> C.mkProj(p, cr c)

let constr_of_sexp (c : Sexp.t) : Constr.constr =
  _constr_get (constr_of_sexp c)

let sexp_of_constr (c : Constr.constr) : Sexp.t =
  sexp_of_constr (_constr_put c)
