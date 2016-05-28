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

(* Main type to be cloned:

type ('constr, 'types) kind_of_term =
  | Rel       of int
  | Var       of Id.t
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of Sorts.t
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of Name.t * 'types * 'types
  | Lambda    of Name.t * 'types * 'constr
  | LetIn     of Name.t * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of constant puniverses
  | Ind       of inductive puniverses
  | Construct of constructor puniverses
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint
  | Proj      of projection * 'constr
*)

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

(*
let rec constr_reify (c : Constr.constr) : coq_constr =
  let cr  = constr_reify           in
  let cra = Array.map constr_reify in
  let module C = Constr            in
  match C.kind c with
  | C.Rel i              -> Rel(i)
  | C.Var v              -> Var(v)
  | C.Meta(mv)           -> Meta mv
  | C.Evar(ek, csa)      -> Evar (Evar.repr ek, Array.map constr_reify csa)
  | C.Sort(st)           -> Sort (st)
  | C.Cast(cs,_k,ty)     -> Cast(cr cs, cr ty)
  | C.Prod(n,tya,tyr)    -> Prod(n, cr tya, cr tyr)
  | C.Lambda(n,ab,bd)    -> Lambda(n, cr ab, cr bd)
  | C.LetIn(n,u,ab,bd)   -> LetIn(n, cr u, cr ab, cr bd)
  | C.App(hd, al)        -> App(cr hd, cra al)
  | C.Const(p,_)         -> Const (p)
  | C.Ind((p,_),_)       -> Ind (p)
  | C.Construct(((c,_),_),_) -> Construct (c)
  | C.Case(_ci, d, c, ca) -> Case(cr d, cr c, cra ca)
  | C.Fix _              -> Fix "I'm lazy"
  | C.CoFix _            -> CoFix "I'm lazy"
  | C.Proj(p,c)          -> Proj(p, cr c)
*)
