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
let _delayed_open_constr_with_bindings_of_sexp = Sexplib.Conv_error.no_matching_variant_found "delayed_open_constr_with_bindings"

let ser_wit_destruction_arg = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_destruction_arg (Ser_misctypes.sexp_of_with_bindings Ser_constrexpr.sexp_of_constr_expr);
    glb_ser = Ser_tacexpr.sexp_of_destruction_arg (Ser_misctypes.sexp_of_with_bindings Ser_tacexpr.sexp_of_glob_constr_and_expr);
    top_ser = Ser_tacexpr.(sexp_of_destruction_arg _sexp_of_delayed_open_constr_with_bindings);

    raw_des = Ser_tacexpr.destruction_arg_of_sexp (Ser_misctypes.with_bindings_of_sexp Ser_constrexpr.constr_expr_of_sexp);
    glb_des = Ser_tacexpr.destruction_arg_of_sexp (Ser_misctypes.with_bindings_of_sexp Ser_tacexpr.glob_constr_and_expr_of_sexp);
    top_des = Ser_tacexpr.(destruction_arg_of_sexp _delayed_open_constr_with_bindings_of_sexp);
  }

let _sexp_of_tactic_val_t _ = Sexplib.Sexp.Atom "[XXX TACTIC_VAL_T]"
let _tactic_val_t_of_sexp = Sexplib.Conv_error.no_matching_variant_found "tactic_val_t"

let ser_wit_tactic = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_raw_tactic_expr;
    glb_ser = Ser_tacexpr.sexp_of_glob_tactic_expr;
    top_ser = _sexp_of_tactic_val_t;

    raw_des = Ser_tacexpr.raw_tactic_expr_of_sexp;
    glb_des = Ser_tacexpr.glob_tactic_expr_of_sexp;
    top_des = _tactic_val_t_of_sexp;
  }

let ser_wit_ltac = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_raw_tactic_expr;
    glb_ser = Ser_tacexpr.sexp_of_glob_tactic_expr;
    top_ser = Sexplib.Conv.sexp_of_unit;

    raw_des = Ser_tacexpr.raw_tactic_expr_of_sexp;
    glb_des = Ser_tacexpr.glob_tactic_expr_of_sexp;
    top_des = Sexplib.Conv.unit_of_sexp;
  }

(* G_ltac *)
(* Defined in g_ltac but serialized here *)

let ser_wit_ltac_info =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_int;
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;

    raw_des = int_of_sexp;
    glb_des = unit_of_sexp;
    top_des = unit_of_sexp;
  }

let ser_wit_production_item =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = Ser_tacentries.(sexp_of_grammar_tactic_prod_item_expr sexp_of_raw_argument);
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;

    raw_des = Ser_tacentries.(grammar_tactic_prod_item_expr_of_sexp raw_argument_of_sexp);
    glb_des = unit_of_sexp;
    top_des = unit_of_sexp;
  }

let ser_wit_ltac_production_sep =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_string;
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;

    raw_des = string_of_sexp;
    glb_des = unit_of_sexp;
    top_des = unit_of_sexp;
  }

let ser_wit_ltac_selector = Ser_genarg.{
    raw_ser = Ser_vernacexpr.sexp_of_goal_selector;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;

    raw_des = Ser_vernacexpr.goal_selector_of_sexp;
    glb_des = Sexplib.Conv.unit_of_sexp;
    top_des = Sexplib.Conv.unit_of_sexp;
  }

let ser_wit_ltac_tacdef_body = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_tacdef_body;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;

    raw_des = Ser_tacexpr.tacdef_body_of_sexp;
    glb_des = Sexplib.Conv.unit_of_sexp;
    top_des = Sexplib.Conv.unit_of_sexp;
  }

let ser_wit_ltac_tactic_level = Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_int;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;

    raw_des = Sexplib.Conv.int_of_sexp;
    glb_des = Sexplib.Conv.unit_of_sexp;
    top_des = Sexplib.Conv.unit_of_sexp;
  }

let ser_wit_ltac_use_default = Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_bool;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;

    raw_des = Sexplib.Conv.bool_of_sexp;
    glb_des = Sexplib.Conv.unit_of_sexp;
    top_des = Sexplib.Conv.unit_of_sexp
  }

(* From G_auto *)
let ser_wit_auto_using = Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_list Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Sexplib.Conv.sexp_of_list Ser_tactypes.sexp_of_glob_constr_and_expr;
    top_ser = Sexplib.Conv.sexp_of_list Ser_ltac_pretype.sexp_of_closed_glob_constr;

    raw_des = Sexplib.Conv.list_of_sexp Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Sexplib.Conv.list_of_sexp Ser_tactypes.glob_constr_and_expr_of_sexp;
    top_des = Sexplib.Conv.list_of_sexp Ser_ltac_pretype.closed_glob_constr_of_sexp;
  }

let ser_wit_hintbases =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_option (sexp_of_list sexp_of_string);
    glb_ser = sexp_of_option (sexp_of_list sexp_of_string);
    top_ser = sexp_of_option (sexp_of_list Ser_hints.sexp_of_hint_db_name);

    raw_des = option_of_sexp (list_of_sexp string_of_sexp);
    glb_des = option_of_sexp (list_of_sexp string_of_sexp);
    top_des = option_of_sexp (list_of_sexp Ser_hints.hint_db_name_of_sexp);
  }

let ser_wit_hintbases_path =
  Ser_genarg.{
    raw_ser = Ser_hints.(sexp_of_hints_path_gen Ser_libnames.sexp_of_reference);
    glb_ser = Ser_hints.sexp_of_hints_path;
    top_ser = Ser_hints.sexp_of_hints_path;

    raw_des = Ser_hints.(hints_path_gen_of_sexp Ser_libnames.reference_of_sexp);
    glb_des = Ser_hints.hints_path_of_sexp;
    top_des = Ser_hints.hints_path_of_sexp;
  }

let ser_wit_hintbases_path_atom =
  Ser_genarg.{
    raw_ser = Ser_hints.(sexp_of_hints_path_atom_gen Ser_libnames.sexp_of_reference);
    glb_ser = Ser_hints.(sexp_of_hints_path_atom_gen Ser_globnames.sexp_of_global_reference);
    top_ser = Ser_hints.(sexp_of_hints_path_atom_gen Ser_globnames.sexp_of_global_reference);

    raw_des = Ser_hints.(hints_path_atom_gen_of_sexp Ser_libnames.reference_of_sexp);
    glb_des = Ser_hints.(hints_path_atom_gen_of_sexp Ser_globnames.global_reference_of_sexp);
    top_des = Ser_hints.(hints_path_atom_gen_of_sexp Ser_globnames.global_reference_of_sexp);
  }

let ser_wit_opthints =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_option (sexp_of_list sexp_of_string);
    glb_ser = sexp_of_option (sexp_of_list sexp_of_string);
    top_ser = sexp_of_option (sexp_of_list Ser_hints.sexp_of_hint_db_name);

    raw_des = option_of_sexp (list_of_sexp string_of_sexp);
    glb_des = option_of_sexp (list_of_sexp string_of_sexp);
    top_des = option_of_sexp (list_of_sexp Ser_hints.hint_db_name_of_sexp);
  }

(* G_rewrite *)

let ser_wit_binders =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform
    (sexp_of_list Ser_constrexpr.sexp_of_local_binder_expr)
    (list_of_sexp Ser_constrexpr.local_binder_expr_of_sexp)

let ser_wit_glob_constr_with_bindings =
  let open Sexplib.Conv in
  let _sexp_of_interp_sign _ = Sexplib.Sexp.Atom "[XXX FUNCTIONAL VALUE INTERP SIGN]" in
  let _interp_sign_of_sexp = Sexplib.Conv_error.no_matching_variant_found "interp" in
  Ser_genarg.{
    raw_ser = Ser_misctypes.sexp_of_with_bindings Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_misctypes.sexp_of_with_bindings Ser_tacexpr.sexp_of_glob_constr_and_expr;
    top_ser = sexp_of_pair _sexp_of_interp_sign Ser_misctypes.(sexp_of_with_bindings Ser_tacexpr.sexp_of_glob_constr_and_expr);

    raw_des = Ser_misctypes.with_bindings_of_sexp Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Ser_misctypes.with_bindings_of_sexp Ser_tacexpr.glob_constr_and_expr_of_sexp;
    top_des = pair_of_sexp _interp_sign_of_sexp Ser_misctypes.(with_bindings_of_sexp Ser_tacexpr.glob_constr_and_expr_of_sexp)
  }

let ser_wit_rewstrategy =
  let _sexp_of_strategy _ = Sexplib.Sexp.Atom "[XXX OPAQUE STRATEGY]" in
  let _strategy_of_sexp = Sexplib.Conv_error.no_matching_variant_found "strategy" in
  Ser_genarg.{
    raw_ser = Ser_rewrite.sexp_of_strategy_ast Ser_constrexpr.sexp_of_constr_expr Ser_tacexpr.sexp_of_raw_red_expr;
    glb_ser = Ser_rewrite.sexp_of_strategy_ast Ser_tacexpr.sexp_of_glob_constr_and_expr Ser_tacexpr.sexp_of_raw_red_expr;
    top_ser = _sexp_of_strategy;

    raw_des = Ser_rewrite.strategy_ast_of_sexp Ser_constrexpr.constr_expr_of_sexp Ser_tacexpr.raw_red_expr_of_sexp;
    glb_des = Ser_rewrite.strategy_ast_of_sexp Ser_tacexpr.glob_constr_and_expr_of_sexp Ser_tacexpr.raw_red_expr_of_sexp;
    top_des = _strategy_of_sexp;
  }

(* G_rewrite.raw_strategy : (Constrexpr.constr_expr, Tacexpr.raw_red_expr) Rewrite.strategy_ast
 * G_rewrite.glob_strategy: (Tacexpr.glob_constr_and_expr, Tacexpr.raw_red_expr) Rewrite.strategy_ast
 * Ltac_plugin.Rewrite.strategy *)

let ser_wit_debug =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform sexp_of_bool bool_of_sexp


let ser_wit_eauto_search_strategy =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform
    (sexp_of_option Ser_class_tactics.sexp_of_search_strategy)
    (option_of_sexp Ser_class_tactics.search_strategy_of_sexp)

let ser_wit_withtac =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform
    (sexp_of_option Ser_tacexpr.sexp_of_raw_tactic_expr)
    (option_of_sexp Ser_tacexpr.raw_tactic_expr_of_sexp)

let register () =
  Ser_genarg.register_genser Tacarg.wit_destruction_arg ser_wit_destruction_arg;

  Ser_genarg.register_genser Tacarg.wit_tactic ser_wit_tactic;

  Ser_genarg.register_genser Tacarg.wit_ltac   ser_wit_ltac;

  Ser_genarg.register_genser G_ltac.wit_ltac_info ser_wit_ltac_info;

  Ser_genarg.register_genser G_ltac.wit_ltac_production_item ser_wit_production_item;
  Ser_genarg.register_genser G_ltac.wit_ltac_production_sep ser_wit_ltac_production_sep;

  Ser_genarg.register_genser G_ltac.wit_ltac_selector ser_wit_ltac_selector;

  Ser_genarg.register_genser G_ltac.wit_ltac_tacdef_body ser_wit_ltac_tacdef_body;
  Ser_genarg.register_genser G_ltac.wit_ltac_tactic_level ser_wit_ltac_tactic_level;

  Ser_genarg.register_genser G_ltac.wit_ltac_use_default ser_wit_ltac_use_default;

  Ser_genarg.register_genser G_auto.wit_auto_using ser_wit_auto_using;
  Ser_genarg.register_genser G_auto.wit_hintbases ser_wit_hintbases;
  Ser_genarg.register_genser G_auto.wit_hints_path ser_wit_hintbases_path;
  Ser_genarg.register_genser G_auto.wit_hints_path_atom ser_wit_hintbases_path_atom;
  Ser_genarg.register_genser G_auto.wit_opthints ser_wit_opthints;

  Ser_genarg.register_genser G_rewrite.wit_binders ser_wit_binders;
  Ser_genarg.register_genser G_rewrite.wit_glob_constr_with_bindings ser_wit_glob_constr_with_bindings;
  Ser_genarg.register_genser G_rewrite.wit_rewstrategy ser_wit_rewstrategy;

  Ser_genarg.register_genser G_class.wit_debug ser_wit_debug;
  Ser_genarg.register_genser G_class.wit_eauto_search_strategy ser_wit_eauto_search_strategy;

  Ser_genarg.register_genser G_obligations.wit_withtac ser_wit_withtac;

  ()

