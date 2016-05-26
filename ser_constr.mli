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


module C = Constr
module N = Names

type coq_name = NS of string | Anonymous

val coq_name_of_sexp : Sexplib.Sexp.t -> coq_name
val sexp_of_coq_name : coq_name -> Sexplib.Sexp.t

type coq_sort = Prop | Type

val coq_sort_of_sexp : Sexplib.Sexp.t -> coq_sort
val sexp_of_coq_sort : coq_sort -> Sexplib.Sexp.t

type coq_constr =
    Rel       of int
  | Var       of string
  | Meta      of int
  | Evar      of int * coq_constr array
  | Sort      of coq_sort
  | Cast      of coq_constr * coq_types
  | Prod      of coq_name * coq_types * coq_types
  | Lambda    of coq_name * coq_types * coq_constr
  | LetIn     of coq_name * coq_constr * coq_types * coq_constr
  | App       of coq_constr * coq_constr array
  | Const     of string
  | Ind       of string
  | Construct of string
  | Case      of coq_constr * coq_constr * coq_constr array
  | Fix       of string
  | CoFix     of string
  | Proj      of string * coq_constr

and coq_types = coq_constr

val coq_constr_of_sexp : Sexplib.Sexp.t -> coq_types
val sexp_of_coq_constr : coq_types -> Sexplib.Sexp.t

val coq_types_of_sexp : Sexplib.Sexp.t -> coq_types
val sexp_of_coq_types : coq_types -> Sexplib.Sexp.t

val name_reify : N.Name.t -> coq_name
val sort_reify : Sorts.t -> coq_sort
val constr_reify : C.constr -> coq_types
