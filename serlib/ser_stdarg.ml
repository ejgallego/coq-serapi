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

open Sexplib.Conv

let ser_wit_int    = Ser_genarg.mk_uniform sexp_of_int int_of_sexp
let ser_wit_bool   = Ser_genarg.mk_uniform sexp_of_bool bool_of_sexp
let ser_wit_string = Ser_genarg.mk_uniform sexp_of_string string_of_sexp
let ser_wit_ident  = Ser_genarg.mk_uniform Ser_names.Id.sexp_of_t Ser_names.Id.t_of_sexp

let ser_wit_constr = Ser_genarg.{
    raw_ser = Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_tactypes.sexp_of_glob_constr_and_expr;
    top_ser = Ser_eConstr.sexp_of_t;

    raw_des = Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Ser_tactypes.glob_constr_and_expr_of_sexp;
    top_des = Ser_eConstr.t_of_sexp;
  }

let ser_wit_uconstr = Ser_genarg.{
    raw_ser = Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_tactypes.sexp_of_glob_constr_and_expr;
    top_ser = Ser_glob_term.sexp_of_closed_glob_constr;

    raw_des = Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Ser_tactypes.glob_constr_and_expr_of_sexp;
    top_des = Ser_glob_term.closed_glob_constr_of_sexp;
  }

let register () =
  Ser_genarg.register_genser Stdarg.wit_string ser_wit_string;
  Ser_genarg.register_genser Stdarg.wit_int ser_wit_int;
  Ser_genarg.register_genser Stdarg.wit_bool ser_wit_bool;
  Ser_genarg.register_genser Stdarg.wit_ident ser_wit_ident;

  Ser_genarg.register_genser Stdarg.wit_constr ser_wit_constr;
  Ser_genarg.register_genser Stdarg.wit_uconstr ser_wit_uconstr

