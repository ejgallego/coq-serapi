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

let ser_wit_constr = Ser_genarg.{
    raw_ser = Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_tactypes.sexp_of_glob_constr_and_expr;
    top_ser = Ser_eConstr.sexp_of_t;
  }

let register () =
  Ser_genarg.register_genser Stdarg.wit_constr ser_wit_constr

