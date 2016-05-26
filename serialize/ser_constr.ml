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

type coq_constr =
  | Rel       of int
  | Var       of id
  | Meta      of int
  | Evar      of int * coq_constr array
  | Sort      of sort
  | Cast      of coq_constr *  (* C.cast_kind * *) coq_types
  | Prod      of name * coq_types * coq_types
  | Lambda    of name * coq_types * coq_constr
  | LetIn     of name * coq_constr * coq_types * coq_constr
  | App       of coq_constr * coq_constr array
  | Const     of constant
  | Ind       of mutind
  | Construct of mutind
  | Case      of (* C.case_info *  *) coq_constr * coq_constr * coq_constr array
  | Fix       of string        (* XXX: I'm lazy *)
  | CoFix     of string        (* XXX: I'm lazy *)
  | Proj      of projection * coq_constr
and coq_types = coq_constr [@@deriving sexp]

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
