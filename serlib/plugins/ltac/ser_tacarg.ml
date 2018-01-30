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

open Ltac_plugin

let _sexp_of_tactic_val_t _ = Sexplib.Sexp.Atom "XXX TACTIC_VAL_T"

let ser_wit_tactic = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_raw_tactic_expr;
    glb_ser = Ser_tacexpr.sexp_of_glob_tactic_expr;
    (* top_ser = Ser_tacexpr.sexp_of_tactic_val_t; *)
    top_ser = _sexp_of_tactic_val_t;
  }

let ser_wit_ltac = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_raw_tactic_expr;
    glb_ser = Ser_tacexpr.sexp_of_glob_tactic_expr;
    top_ser = Sexplib.Conv.sexp_of_unit;
  }

(* (constr_expr with_bindings Tacexpr.destruction_arg,
 *  glob_constr_and_expr with_bindings Tacexpr.destruction_arg,
 *  delayed_open_constr_with_bindings Tacexpr.destruction_arg) genarg_type *)
let _ser_wit_destruction_arg = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_raw_tactic_expr;
    glb_ser = Ser_tacexpr.sexp_of_glob_tactic_expr;
    top_ser = Sexplib.Conv.sexp_of_unit;
  }

(* Defined in g_ltac but serialized here *)
let ser_wit_ltac_selector = Ser_genarg.{
    raw_ser = Ser_vernacexpr.sexp_of_goal_selector;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;
  }

let ser_wit_ltac_use_default = Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_bool;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;
  }

let ser_wit_ltac_tacdef_body = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_tacdef_body;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;
  }

let ser_wit_ltac_tactic_level = Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_int;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;
  }

let ser_wit_auto_using = Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_list Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Sexplib.Conv.sexp_of_list Ser_tactypes.sexp_of_glob_constr_and_expr;
    top_ser = Sexplib.Conv.sexp_of_list Ser_glob_term.sexp_of_closed_glob_constr;
  }

let ser_wit_hintbases =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_option (sexp_of_list sexp_of_string);
    glb_ser = sexp_of_option (sexp_of_list sexp_of_string);
    top_ser = sexp_of_option (sexp_of_list Ser_hints.sexp_of_hint_db_name);
  }

let register () =
  (* Ser_genarg.register_genprint Tacarg.wit_destruction_arg ser_wit_destruction_arg; *)
  Ser_genarg.register_genprint Tacarg.wit_tactic ser_wit_tactic;
  Ser_genarg.register_genprint Tacarg.wit_ltac   ser_wit_ltac;

  Ser_genarg.register_genprint G_ltac.wit_ltac_selector ser_wit_ltac_selector;
  Ser_genarg.register_genprint G_ltac.wit_ltac_use_default ser_wit_ltac_use_default;
  Ser_genarg.register_genprint G_ltac.wit_ltac_tacdef_body ser_wit_ltac_tacdef_body;
  Ser_genarg.register_genprint G_ltac.wit_ltac_tactic_level ser_wit_ltac_tactic_level;

  Ser_genarg.register_genprint G_auto.wit_auto_using ser_wit_auto_using;
  Ser_genarg.register_genprint G_auto.wit_hintbases ser_wit_hintbases;
  ()

