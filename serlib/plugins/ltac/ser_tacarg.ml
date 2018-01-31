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

(* Tacarg *)
let _sexp_of_delayed_open_constr_with_bindings _ = Sexplib.Sexp.Atom "[XXX FUNCTIONAL VALUE DELAYED OPEN CONSTR]"

let ser_wit_destruction_arg = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_destruction_arg (Ser_misctypes.sexp_of_with_bindings Ser_constrexpr.sexp_of_constr_expr);
    glb_ser = Ser_tacexpr.sexp_of_destruction_arg (Ser_misctypes.sexp_of_with_bindings Ser_tacexpr.sexp_of_glob_constr_and_expr);
    top_ser = Ser_tacexpr.(sexp_of_destruction_arg _sexp_of_delayed_open_constr_with_bindings);
  }

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

(* G_ltac *)
(* Defined in g_ltac but serialized here *)

let ser_wit_ltac_info =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_int;
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;
  }

let ser_wit_production_item =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = Ser_tacentries.(sexp_of_grammar_tactic_prod_item_expr sexp_of_raw_argument);
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;
  }

let ser_wit_ltac_production_sep =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_string;
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;
  }

let ser_wit_ltac_selector = Ser_genarg.{
    raw_ser = Ser_vernacexpr.sexp_of_goal_selector;
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

let ser_wit_ltac_use_default = Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_bool;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;
  }

(* From G_auto *)
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

let ser_wit_hintbases_path =
  Ser_genarg.{
    raw_ser = Ser_hints.(sexp_of_hints_path_gen Ser_libnames.sexp_of_reference);
    glb_ser = Ser_hints.sexp_of_hints_path;
    top_ser = Ser_hints.sexp_of_hints_path;
  }

let ser_wit_hintbases_path_atom =
  Ser_genarg.{
    raw_ser = Ser_hints.(sexp_of_hints_path_atom_gen Ser_libnames.sexp_of_reference);
    glb_ser = Ser_hints.(sexp_of_hints_path_atom_gen Ser_globnames.sexp_of_global_reference);
    top_ser = Ser_hints.(sexp_of_hints_path_atom_gen Ser_globnames.sexp_of_global_reference);
  }

let ser_wit_opthints =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_option (sexp_of_list sexp_of_string);
    glb_ser = sexp_of_option (sexp_of_list sexp_of_string);
    top_ser = sexp_of_option (sexp_of_list Ser_hints.sexp_of_hint_db_name);
  }

let register () =
  Ser_genarg.register_genprint Tacarg.wit_destruction_arg ser_wit_destruction_arg;
  Ser_genarg.register_genprint Tacarg.wit_tactic ser_wit_tactic;
  Ser_genarg.register_genprint Tacarg.wit_ltac   ser_wit_ltac;

  Ser_genarg.register_genprint G_ltac.wit_ltac_info ser_wit_ltac_info;
  Ser_genarg.register_genprint G_ltac.wit_ltac_production_item ser_wit_production_item;
  Ser_genarg.register_genprint G_ltac.wit_ltac_production_sep ser_wit_ltac_production_sep;
  Ser_genarg.register_genprint G_ltac.wit_ltac_selector ser_wit_ltac_selector;
  Ser_genarg.register_genprint G_ltac.wit_ltac_tacdef_body ser_wit_ltac_tacdef_body;
  Ser_genarg.register_genprint G_ltac.wit_ltac_tactic_level ser_wit_ltac_tactic_level;
  Ser_genarg.register_genprint G_ltac.wit_ltac_use_default ser_wit_ltac_use_default;

  Ser_genarg.register_genprint G_auto.wit_auto_using ser_wit_auto_using;
  Ser_genarg.register_genprint G_auto.wit_hintbases ser_wit_hintbases;
  Ser_genarg.register_genprint G_auto.wit_hints_path ser_wit_hintbases_path;
  Ser_genarg.register_genprint G_auto.wit_hints_path_atom ser_wit_hintbases_path_atom;
  Ser_genarg.register_genprint G_auto.wit_opthints ser_wit_opthints;

(* TODO

  G_rewrite.wit_binders
  G_rewrite.wit_glob_constr_with_bindings
  G_rewrite.wit_rewstrategy

  G_class.wit_debug
  G_class.wit_eauto_search_strategy

  G_obligations.wit_withtac
*)
  ()

