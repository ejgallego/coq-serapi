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

open Sexplib.Std

open Ser_bigint
open Ser_loc
open Ser_names
open Ser_misctypes
open Ser_decl_kinds
open Ser_evar_kinds
open Ser_genarg
open Ser_libnames
open Ser_glob_term

type notation =  [%import: Constrexpr.notation]
  [@@deriving sexp]

type explicitation = [%import: Constrexpr.explicitation
     [@with Loc.t        := loc;
            Loc.located  := located;
            Names.Id.t   := id;
            Names.Name.t := name;
     ]]
  [@@deriving sexp]

type binder_kind = [%import: Constrexpr.binder_kind
     [@with Decl_kinds.binding_kind := binding_kind;
     ]]
  [@@deriving sexp]

type abstraction_kind = [%import: Constrexpr.abstraction_kind]
  [@@deriving sexp]

type proj_flag = [%import: Constrexpr.proj_flag]
  [@@deriving sexp]

type prim_token = [%import: Constrexpr.prim_token
     [@with Bigint.bigint := bigint;
     ]]
  [@@deriving sexp]

type cases_pattern_expr = [%import: Constrexpr.cases_pattern_expr
     [@with Loc.t        := loc;
            Loc.located  := located;

            Names.Id.t   := id;
            Libnames.reference   := reference;
     ]]
and cases_pattern_notation_substitution = [%import: Constrexpr.cases_pattern_notation_substitution
    [@with Loc.t        := loc;
           Loc.located  := located;
    ]]
  [@@deriving sexp]

type instance_expr = [%import: Constrexpr.instance_expr
  [@with Misctypes.glob_level := glob_level;
         Libnames.reference   := reference;
  ]]
  [@@deriving sexp]

type constr_expr = [%import: Constrexpr.constr_expr
     [@with Loc.t        := loc;
            Loc.located  := located;

            Names.Id.t   := id;
            Names.Name.t := name;

            Decl_kinds.binding_kind := binding_kind;

            Evar_kinds.t         := evar_kinds;

            Libnames.reference   := reference;

            Misctypes.case_style := case_style;
            Misctypes.cast_type  := cast_type;
            Misctypes.glob_sort  := glob_sort;
            Misctypes.intro_pattern_naming_expr := intro_pattern_naming_expr;
            Misctypes.patvar     := patvar;

            Genarg.raw_generic_argument := raw_generic_argument;

            Glob_term.existential_name  := existential_name;
     ]]

and case_expr   = [%import: Constrexpr.case_expr
    [@with Loc.t        := loc;
           Loc.located  := located;
           Names.Id.t   := id;
           Names.Name.t := name;
    ]]
and branch_expr = [%import: Constrexpr.branch_expr
    [@with Loc.t        := loc;
           Loc.located  := located;
    ]]
and binder_expr = [%import: Constrexpr.binder_expr
    [@with Loc.t        := loc;
           Loc.located  := located;
           Names.Id.t   := id;
           Names.Name.t := name;
    ]]
and fix_expr    = [%import: Constrexpr.fix_expr
    [@with Loc.t        := loc;
           Loc.located  := located;
           Names.Id.t   := id;
    ]]
and cofix_expr  = [%import: Constrexpr.cofix_expr
    [@with Loc.t        := loc;
           Loc.located  := located;
           Names.Id.t   := id;
    ]]
and recursion_order_expr = [%import: Constrexpr.recursion_order_expr
    [@with Loc.t        := loc;
           Loc.located  := located;
           Names.Id.t   := id;
    ]]
and local_binder         = [%import: Constrexpr.local_binder
    [@with Loc.t        := loc;
           Loc.located  := located;
           Names.Id.t   := id;
           Names.Name.t := name;
    ]]
and constr_notation_substitution = [%import: Constrexpr.constr_notation_substitution]
  [@@deriving sexp]
