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

open Ser_names
open Ser_globnames
open Ser_loc
open Ser_misctypes
open Ser_decl_kinds
open Ser_genarg
open Ser_evar_kinds

(**********************************************************************)
(* Glob_term                                                          *)
(**********************************************************************)

type existential_name = Glob_term.existential_name
let existential_name_of_sexp = id_of_sexp
let sexp_of_existential_name = sexp_of_id

type cases_pattern = [%import: Glob_term.cases_pattern
                     [@with Loc.t               := loc;
                            Names.Name.t        := name;
                            Names.constructor   := constructor
                     ]]
           [@@deriving sexp]


type glob_constr = [%import: Glob_term.glob_constr
                   [@with Loc.t               := loc;
                          Names.Id.t          := id;
                          Names.Name.t        := name;

                          Evar_kinds.t        := evar_kinds;

                          Globnames.global_reference := global_reference;

                          Misctypes.case_style := case_style;
                          Misctypes.cast_type  := cast_type;
                          Misctypes.glob_level := glob_level;
                          Misctypes.glob_sort  := glob_sort;
                          Misctypes.patvar     := patvar;
                          Misctypes.intro_pattern_naming_expr := intro_pattern_naming_expr;
                          Genarg.glob_generic_argument := glob_generic_argument;

                          Decl_kinds.binding_kind := binding_kind;
                   ]]
and glob_decl    = [%import: Glob_term.glob_decl
                   [@with Loc.t               := loc;
                          Names.Id.t          := id;
                          Names.Name.t        := name;
                          Decl_kinds.binding_kind := binding_kind;
                   ]]

and fix_recursion_order = [%import: Glob_term.fix_recursion_order]
and fix_kind            = [%import: Glob_term.fix_kind]
and predicate_pattern   = [%import: Glob_term.predicate_pattern
                          [@with Loc.t               := loc;
                                 Names.Id.t          := id;
                                 Names.Name.t        := name;
                                 Names.inductive     := inductive;
                                 Decl_kinds.binding_kind := binding_kind;
                          ]]

and tomatch_tuple  = [%import: Glob_term.tomatch_tuple]
and tomatch_tuples = [%import: Glob_term.tomatch_tuples]
and cases_clause   = [%import: Glob_term.cases_clause
                     [@with Loc.t               := loc;
                            Names.Id.t          := id;
                            Names.Name.t        := name;
                     ]]

and cases_clauses  = [%import: Glob_term.cases_clauses]
  [@@deriving sexp]

