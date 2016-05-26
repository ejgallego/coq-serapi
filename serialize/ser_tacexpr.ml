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

open Sexplib
open Sexplib.Std

open Ser_loc
open Ser_names
open Ser_misctypes
open Ser_locus
(* open Ser_genredexpr *)
(* open Ser_decl_kinds *)
(* open Ser_evar_kinds *)
(* open Ser_genarg *)
(* open Ser_libnames *)
(* open Ser_glob_term *)
(* open Ser_constrexpr *)

type direction_flag =
  [%import: Tacexpr.direction_flag]
  [@@deriving sexp]

type lazy_flag =
  [%import: Tacexpr.lazy_flag]
  [@@deriving sexp]

type global_flag =
  [%import: Tacexpr.global_flag]
  [@@deriving sexp]

type evars_flag =
  [%import: Tacexpr.evars_flag]
  [@@deriving sexp]

type rec_flag =
  [%import: Tacexpr.rec_flag]
  [@@deriving sexp]

type advanced_flag =
  [%import: Tacexpr.advanced_flag]
  [@@deriving sexp]

type letin_flag =
  [%import: Tacexpr.letin_flag]
  [@@deriving sexp]

type clear_flag =
  [%import: Tacexpr.clear_flag]
  [@@deriving sexp]

type debug =
  [%import: Tacexpr.debug]
  [@@deriving sexp]

type 'a core_induction_arg =
  [%import: 'a Tacexpr.core_induction_arg
  [@with
    Loc.t       := loc;
    Loc.located := located;
    Names.Id.t  := id;
  ]]
  [@@deriving sexp]

type 'a induction_arg =
  [%import: 'a Tacexpr.induction_arg]
  [@@deriving sexp]

type inversion_kind =
  [%import: Tacexpr.inversion_kind]
  [@@deriving sexp]

type ('c,'d,'id) inversion_strength =
  [%import: ('c,'d,'id) Tacexpr.inversion_strength
  [@with
    Loc.t       := loc;
    Loc.located := located;
    Names.Id.t  := id;
    Misctypes.or_var := or_var;
    Misctypes.or_and_intro_pattern_expr := or_and_intro_pattern_expr;
  ]]
  [@@deriving sexp]

type ('a,'b) location =
  [%import: ('a, 'b) Tacexpr.location]
  [@@deriving sexp]

type 'id message_token =
  [%import: ('id) Tacexpr.message_token]
  [@@deriving sexp]

type ('dconstr,'id) induction_clause =
  [%import: ('dconstr,'id) Tacexpr.induction_clause
  [@with
    Loc.t       := loc;
    Loc.located := located;
    Names.Id.t  := id;
    Misctypes.or_var := or_var;
    Misctypes.with_bindings := with_bindings;
    Misctypes.intro_pattern_naming_expr := intro_pattern_naming_expr;
    Misctypes.or_and_intro_pattern_expr := or_and_intro_pattern_expr;
    Locus.clause_expr := clause_expr;
  ]]
  [@@deriving sexp]

type ('constr,'dconstr,'id) induction_clause_list =
  [%import: ('constr,'dconstr,'id) Tacexpr.induction_clause_list
  [@with
    Loc.t       := loc;
    Loc.located := located;
    Names.Id.t  := id;
    Misctypes.or_var := or_var;
    Misctypes.with_bindings := with_bindings;
    Misctypes.intro_pattern_naming_expr := intro_pattern_naming_expr;
    Misctypes.or_and_intro_pattern_expr := or_and_intro_pattern_expr;
    Locus.clause_expr := clause_expr;
  ]]
  [@@deriving sexp]

type 'a with_bindings_arg =
  [%import: 'a Tacexpr.with_bindings_arg
  [@with
     Misctypes.with_bindings := with_bindings;
  ]]
  [@@deriving sexp]

type multi =
  [%import: Tacexpr.multi]
  [@@deriving sexp]

type 'a match_pattern =
  [%import: 'a Tacexpr.match_pattern
  [@with
    Loc.t       := loc;
    Loc.located := located;
    Names.Id.t  := id;
    Names.Name.t  := name;
  ]]
  [@@deriving sexp]

type 'a match_context_hyps =
  [%import: 'a Tacexpr.match_context_hyps
  [@with
    Loc.t       := loc;
    Loc.located := located;
    Names.Id.t  := id;
    Names.Name.t  := name;
  ]]
  [@@deriving sexp]

type ('a,'t) match_rule =
  [%import: ('a, 't) Tacexpr.match_rule
  [@with
    Loc.t       := loc;
    Loc.located := located;
    Names.Id.t  := id;
    Names.Name.t  := name;
  ]]
  [@@deriving sexp]

type ml_tactic_name =
  [%import: Tacexpr.ml_tactic_name]
  [@@deriving sexp]

(* This is beyond import and sexp for the moment *)
(*
type 'a gen_atomic_tactic_expr = 'a Tacexpr.gen_atomic_tactic_expr =
  (* Basic tactics *)
  | TacIntroPattern of 'dtrm intro_pattern_expr located list
  | TacIntroMove of id option * 'nam move_location
  | TacExact of 'trm
  | TacApply of advanced_flag * evars_flag * 'trm with_bindings_arg list *
      ('nam * 'dtrm intro_pattern_expr located option) option
  | TacElim of evars_flag * 'trm with_bindings_arg * 'trm with_bindings option
  | TacCase of evars_flag * 'trm with_bindings_arg
  | TacFix of id option * int
  | TacMutualFix of id * int * (id * int * 'trm) list
  | TacCofix of id option
  | TacMutualCofix of id * (id * 'trm) list
  | TacAssert of
      bool * 'tacexpr option *
      'dtrm intro_pattern_expr located option * 'trm
  | TacGeneralize of ('trm with_occurrences * name) list
  | TacGeneralizeDep of 'trm
  | TacLetTac of name * 'trm * 'nam clause_expr * letin_flag *
      intro_pattern_naming_expr located option

  (* Derived basic tactics *)
  | TacInductionDestruct of
      rec_flag * evars_flag * ('trm,'dtrm,'nam) induction_clause_list
  | TacDoubleInduction of quantified_hypothesis * quantified_hypothesis

  (* Automation tactics *)
  | TacTrivial of debug * 'trm list * string list option
  | TacAuto of debug * int or_var option * 'trm list * string list option

  (* Context management *)
  | TacClear of bool * 'nam list
  | TacClearBody of 'nam list
  | TacMove of 'nam * 'nam move_location
  | TacRename of ('nam *'nam) list

  (* Trmuctors *)
  | TacSplit of evars_flag * 'trm bindings list

  (* Conversion *)
  | TacReduce of ('trm,'cst,'pat) red_expr_gen * 'nam clause_expr
  | TacChange of 'pat option * 'dtrm * 'nam clause_expr

  (* Equivalence relations *)
  | TacSymmetry of 'nam clause_expr

  (* Equality and inversion *)
  | TacRewrite of evars_flag *
      (bool * multi * 'dtrm with_bindings_arg) list * 'nam clause_expr *
      (* spiwack: using ['dtrm] here is a small hack, may not be
         stable by a change in the representation of delayed
         terms. Because, in fact, it is the whole "with_bindings"
         which is delayed. But because the "t" level for ['dtrm] is
         uninterpreted, it works fine here too, and avoid more
         disruption of this file. *)
      'tacexpr option
  | TacInversion of ('trm,'dtrm,'nam) inversion_strength * quantified_hypothesis

constraint 'a = <
    term:'trm;
    utrm: 'utrm;
    dterm: 'dtrm;
    pattern:'pat;
    constant:'cst;
    reference:'ref;
    name:'nam;
    tacexpr:'tacexpr;
    level:'lev
>

(** Possible arguments of a tactic definition *)

and 'a gen_tactic_arg =
  | TacDynamic     of Loc.t * Dyn.t
  | TacGeneric     of 'lev generic_argument
  | MetaIdArg      of Loc.t * bool * string
  | ConstrMayEval  of ('trm,'cst,'pat) may_eval
  | UConstr        of 'utrm
  | Reference      of 'ref
  | TacCall of Loc.t * 'ref *
      'a gen_tactic_arg list
  | TacFreshId of string or_var list
  | Tacexp of 'tacexpr
  | TacPretype of 'trm
  | TacNumgoals

constraint 'a = <
    term:'trm;
    utrm: 'utrm;
    dterm: 'dtrm;
    pattern:'pat;
    constant:'cst;
    reference:'ref;
    name:'nam;
    tacexpr:'tacexpr;
    level:'lev
>

(** Generic ltac expressions.
    't : terms, 'p : patterns, 'c : constants, 'i : inductive,
    'r : ltac refs, 'n : idents, 'l : levels *)

and 'a gen_tactic_expr =
  | TacAtom of Loc.t * 'a gen_atomic_tactic_expr
  | TacThen of
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacDispatch of
      'a gen_tactic_expr list
  | TacExtendTac of
      'a gen_tactic_expr array *
      'a gen_tactic_expr *
      'a gen_tactic_expr array
  | TacThens of
      'a gen_tactic_expr *
      'a gen_tactic_expr list
  | TacThens3parts of
      'a gen_tactic_expr *
      'a gen_tactic_expr array *
      'a gen_tactic_expr *
      'a gen_tactic_expr array
  | TacFirst of 'a gen_tactic_expr list
  | TacComplete of 'a gen_tactic_expr
  | TacSolve of 'a gen_tactic_expr list
  | TacTry of 'a gen_tactic_expr
  | TacOr of
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacOnce of
      'a gen_tactic_expr
  | TacExactlyOnce of
      'a gen_tactic_expr
  | TacIfThenCatch of
      'a gen_tactic_expr *
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacOrelse of
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacDo of int or_var * 'a gen_tactic_expr
  | TacTimeout of int or_var * 'a gen_tactic_expr
  | TacTime of string option * 'a gen_tactic_expr
  | TacRepeat of 'a gen_tactic_expr
  | TacProgress of 'a gen_tactic_expr
  | TacShowHyps of 'a gen_tactic_expr
  | TacAbstract of
      'a gen_tactic_expr * id option
  | TacId of 'n message_token list
  | TacFail of global_flag * int or_var * 'n message_token list
  | TacInfo of 'a gen_tactic_expr
  | TacLetIn of rec_flag *
      (id located * 'a gen_tactic_arg) list *
      'a gen_tactic_expr
  | TacMatch of lazy_flag *
      'a gen_tactic_expr *
      ('p,'a gen_tactic_expr) match_rule list
  | TacMatchGoal of lazy_flag * direction_flag *
      ('p,'a gen_tactic_expr) match_rule list
  | TacFun of 'a gen_tactic_fun_ast
  | TacArg of 'a gen_tactic_arg located
  (* For ML extensions *)
  | TacML of loc * ml_tactic_name * 'l generic_argument list
  (* For syntax extensions *)
  | TacAlias of loc * kername * (id * 'l generic_argument) list

constraint 'a = <
    term:'t;
    utrm: 'utrm;
    dterm: 'dtrm;
    pattern:'p;
    constant:'c;
    reference:'r;
    name:'n;
    tacexpr:'tacexpr;
    level:'l
>

and 'a gen_tactic_fun_ast =
    id option list * 'a gen_tactic_expr

constraint 'a = <
    term: 't;
    utrm: 'utrm;
    dterm: 'dtrm;
    pattern:'p;
    constant:'c;
    reference:'r;
    name:'n;
    tacexpr:'te;
    level:'l
>
*)
(* [%import: 'a Tacexpr.gen_atomic_tactic_expr] *)
(*   [@@deriving sexp] *)

type raw_tactic_expr = Tacexpr.raw_tactic_expr

let raw_tactic_expr_of_sexp _rawt = Obj.magic 0
let sexp_of_raw_tactic_expr _sexp = Sexp.Atom ""

type raw_red_expr = Tacexpr.raw_red_expr

let raw_red_expr_of_sexp _rawt = Obj.magic 0
let sexp_of_raw_red_expr _sexp = Sexp.Atom ""
