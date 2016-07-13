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
open Ser_nametab
(* open Ser_decl_kinds *)
(* open Ser_evar_kinds *)
open Ser_constr
open Ser_genarg
open Ser_libnames
open Ser_genredexpr
open Ser_glob_term
open Ser_pattern
open Ser_constrexpr

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

type goal_selector =
  [%import: Tacexpr.goal_selector
  [@with
    Names.Id.t  := id;
  ]]
  [@@deriving sexp]

type 'a core_destruction_arg =
  [%import: 'a Tacexpr.core_destruction_arg
  [@with
    Loc.t       := loc;
    Loc.located := located;
    Names.Id.t  := id;
  ]]
  [@@deriving sexp]

type 'a destruction_arg =
  [%import: 'a Tacexpr.destruction_arg]
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

type ml_tactic_entry =
  [%import: Tacexpr.ml_tactic_entry]
  [@@deriving sexp]

(* type dyn = Ser_Dyn [@@deriving sexp] *)
(* let to_dyn _   = Ser_Dyn *)
(* let from_dyn _ = fst (Dyn.create "dyn_tac") 0 *)

(* This is beyond import and sexp for the moment, see:
 * https://github.com/janestreet/ppx_sexp_conv/issues/6
 *)
(* We thus iso-project the tactic definition in a virtually identical copy (but for the Dyn) *)
module ITac = struct

type ('trm, 'dtrm, 'pat, 'cst, 'ref, 'nam, 'tacexpr, 'lev) gen_atomic_tactic_expr =
  | TacIntroPattern of evars_flag * 'dtrm intro_pattern_expr located list
  | TacApply of advanced_flag * evars_flag * 'trm with_bindings_arg list *
      ('nam * 'dtrm intro_pattern_expr located option) option
  | TacElim of evars_flag * 'trm with_bindings_arg * 'trm with_bindings option
  | TacCase of evars_flag * 'trm with_bindings_arg
  | TacMutualFix of id * int * (id * int * 'trm) list
  | TacMutualCofix of id * (id * 'trm) list
  | TacAssert of
      bool * 'tacexpr option option *
      'dtrm intro_pattern_expr located option * 'trm
  | TacGeneralize of ('trm with_occurrences * name) list
  | TacLetTac of name * 'trm * 'nam clause_expr * letin_flag *
      intro_pattern_naming_expr located option
  | TacInductionDestruct of
      rec_flag * evars_flag * ('trm,'dtrm,'nam) induction_clause_list
  | TacReduce of ('trm,'cst,'pat) red_expr_gen * 'nam clause_expr
  | TacChange of 'pat option * 'dtrm * 'nam clause_expr
  | TacRewrite of evars_flag *
      (bool * multi * 'dtrm with_bindings_arg) list * 'nam clause_expr *
      'tacexpr option
  | TacInversion of ('trm,'dtrm,'nam) inversion_strength * quantified_hypothesis

and ('trm, 'dtrm, 'pat, 'cst, 'ref, 'nam, 'tacexpr, 'lev) gen_tactic_arg =
  | TacGeneric     of 'lev generic_argument
  | ConstrMayEval  of ('trm,'cst,'pat) may_eval
  | Reference      of 'ref
  | TacCall        of loc * 'ref *
      ('trm, 'dtrm, 'pat, 'cst, 'ref, 'nam, 'tacexpr, 'lev) gen_tactic_arg list
  | TacFreshId of string or_var list
  | Tacexp of 'tacexpr
  | TacPretype of 'trm
  | TacNumgoals
and ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr =
  | TacAtom of loc * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_atomic_tactic_expr
  | TacThen of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacDispatch of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr list
  | TacExtendTac of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr array *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr array
  | TacThens of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr list
  | TacThens3parts of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr array *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr array
  | TacFirst of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr list
  | TacComplete of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacSolve of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr list
  | TacTry of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacOr of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacOnce of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacExactlyOnce of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacIfThenCatch of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacOrelse of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacDo of int or_var * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacTimeout of int or_var * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacTime of string option * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacRepeat of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacProgress of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacShowHyps of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacAbstract of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr * id option
  | TacId of 'n message_token list
  | TacFail of global_flag * int or_var * 'n message_token list
  | TacInfo of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacLetIn of rec_flag *
      (id located * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_arg) list *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacMatch of lazy_flag *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('p,('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr) match_rule list
  | TacMatchGoal of lazy_flag * direction_flag *
      ('p,('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr) match_rule list
  | TacFun of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_fun_ast
  | TacArg of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_arg located
  | TacSelect of goal_selector * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacML     of loc * ml_tactic_entry * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_arg list
  | TacAlias  of loc * kername * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_arg list

and ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_fun_ast =
    id option list * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
   [@@deriving sexp]

end

let rec _gen_atom_tactic_expr_put (t : 'a Tacexpr.gen_atomic_tactic_expr) :
  ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_atomic_tactic_expr = match t with
  | Tacexpr.TacIntroPattern(a,b)         -> ITac.TacIntroPattern(a,b)
  | Tacexpr.TacApply (a,b,c,d)           -> ITac.TacApply (a,b,c,d)
  | Tacexpr.TacElim (a,b,c)              -> ITac.TacElim (a,b,c)
  | Tacexpr.TacCase (a,b)                -> ITac.TacCase (a,b)
  | Tacexpr.TacMutualFix (a,b,c)         -> ITac.TacMutualFix (a,b,c)
  | Tacexpr.TacMutualCofix (a,b)         -> ITac.TacMutualCofix (a,b)
  | Tacexpr.TacAssert (a,b,c,d)          -> ITac.TacAssert (a,b,c,d)
  | Tacexpr.TacGeneralize a              -> ITac.TacGeneralize a
  | Tacexpr.TacLetTac (a,b,c,d,e)        -> ITac.TacLetTac (a,b,c,d,e)
  | Tacexpr.TacInductionDestruct (a,b,c) -> ITac.TacInductionDestruct (a,b,c)
  | Tacexpr.TacReduce (a,b)              -> ITac.TacReduce (a,b)
  | Tacexpr.TacChange (a,b,c)            -> ITac.TacChange (a,b,c)
  | Tacexpr.TacRewrite (a,b,c,d)         -> ITac.TacRewrite (a,b,c,d)
  | Tacexpr.TacInversion (a,b)           -> ITac.TacInversion (a,b)
and _gen_tactic_arg_put (t : 'a Tacexpr.gen_tactic_arg) :
  ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_arg = match t with
  | Tacexpr.TacGeneric a      -> ITac.TacGeneric a
  | Tacexpr.ConstrMayEval a   -> ITac.ConstrMayEval a
  | Tacexpr.Reference a       -> ITac.Reference a
  | Tacexpr.TacCall (a,b,c)   -> ITac.TacCall (a,b, List.map _gen_tactic_arg_put c)
  | Tacexpr.TacFreshId a      -> ITac.TacFreshId a
  | Tacexpr.Tacexp a          -> ITac.Tacexp a
  | Tacexpr.TacPretype a      -> ITac.TacPretype a
  | Tacexpr.TacNumgoals       -> ITac.TacNumgoals
and _gen_tactic_expr_put (t : 'a Tacexpr.gen_tactic_expr) :
  ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_expr =
  let u  x = _gen_tactic_expr_put x in
  let uu x = List.map u x           in
  let ua x = Array.map u x          in
  match t with
  | Tacexpr.TacAtom (a,b)            -> ITac.TacAtom (a,_gen_atom_tactic_expr_put b)
  | Tacexpr.TacThen (a,b)            -> ITac.TacThen (u a, u b)
  | Tacexpr.TacDispatch a            -> ITac.TacDispatch (uu a)
  | Tacexpr.TacExtendTac (a,b,c)     -> ITac.TacExtendTac (ua a, u b, ua c)
  | Tacexpr.TacThens (a,b)           -> ITac.TacThens (u a, uu b)
  | Tacexpr.TacThens3parts (a,b,c,d) -> ITac.TacThens3parts (u a, ua b, u c, ua d)
  | Tacexpr.TacFirst a               -> ITac.TacFirst (uu a)
  | Tacexpr.TacComplete a            -> ITac.TacComplete (u a)
  | Tacexpr.TacSolve a               -> ITac.TacSolve (uu a)
  | Tacexpr.TacTry a                 -> ITac.TacTry (u a)
  | Tacexpr.TacOr (a,b)              -> ITac.TacOr (u a, u b)
  | Tacexpr.TacOnce a                -> ITac.TacOnce (u a)
  | Tacexpr.TacExactlyOnce a         -> ITac.TacExactlyOnce (u a)
  | Tacexpr.TacIfThenCatch (a,b,c)   -> ITac.TacIfThenCatch (u a,u b,u c)
  | Tacexpr.TacOrelse (a,b)          -> ITac.TacOrelse (u a,u b)
  | Tacexpr.TacDo (a,b)              -> ITac.TacDo (a,u b)
  | Tacexpr.TacTimeout (a,b)         -> ITac.TacTimeout (a,u b)
  | Tacexpr.TacTime (a,b)            -> ITac.TacTime (a,u b)
  | Tacexpr.TacRepeat a              -> ITac.TacRepeat (u a)
  | Tacexpr.TacProgress a            -> ITac.TacProgress (u a)
  | Tacexpr.TacShowHyps a            -> ITac.TacShowHyps (u a)
  | Tacexpr.TacAbstract (a,b)        -> ITac.TacAbstract (u a,b)
  | Tacexpr.TacId a                  -> ITac.TacId a
  | Tacexpr.TacFail (a,b,c)          -> ITac.TacFail (a,b,c)
  | Tacexpr.TacInfo a                -> ITac.TacInfo (u a)
  (* | TacLetIn of rec_flag * *)
  (*     (Id.t located * 'a gen_tactic_arg) list * *)
  (*     'a gen_tactic_expr *)
  | Tacexpr.TacLetIn (a, l, t) ->
    let _pt = List.map (fun (a,t) -> (a,_gen_tactic_arg_put t)) in
    ITac.TacLetIn (a, _pt l, _gen_tactic_expr_put t)
  (* | TacMatch of lazy_flag * *)
  (*     'a gen_tactic_expr * *)
  (*     ('p,'a gen_tactic_expr) match_rule list *)
  (* type ('a,'t) match_rule = *)
  (* | Pat of 'a match_context_hyps list * 'a match_pattern * 't *)
  (* | All of 't *)
  | Tacexpr.TacMatch (a, e, mr)      ->
    let _pmr = List.map (function
        | Tacexpr.Pat (a,b,t) -> Tacexpr.Pat (a,b,_gen_tactic_expr_put t)
        | Tacexpr.All e       -> Tacexpr.All (_gen_tactic_expr_put e)
      ) in
    ITac.TacMatch(a, _gen_tactic_expr_put e, _pmr mr)
  | Tacexpr.TacMatchGoal (e, d, t)  ->
    let _pmr = List.map (function
        | Tacexpr.Pat (a,b,t) -> Tacexpr.Pat (a,b,_gen_tactic_expr_put t)
        | Tacexpr.All e       -> Tacexpr.All (_gen_tactic_expr_put e)
      ) in
    ITac.TacMatchGoal(e, d, _pmr t)
  | Tacexpr.TacFun a                 -> ITac.TacFun (_gen_tactic_fun_ast_put a)
  | Tacexpr.TacArg (l,a)             -> ITac.TacArg (l, _gen_tactic_arg_put a)
  | Tacexpr.TacSelect(gs,te)         -> ITac.TacSelect(gs, _gen_tactic_expr_put te)
  | Tacexpr.TacML (a,b,c)            -> ITac.TacML (a,b, List.map _gen_tactic_arg_put c)
  | Tacexpr.TacAlias (a,b,c)         -> ITac.TacAlias (a,b, List.map _gen_tactic_arg_put c)
and _gen_tactic_fun_ast_put (t : 'a Tacexpr.gen_tactic_fun_ast) :
  ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_fun_ast =
  match t with
  | (a,b) -> (a, _gen_tactic_expr_put b)

let rec _gen_atom_tactic_expr_get (t : ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_atomic_tactic_expr) :
  'a Tacexpr.gen_atomic_tactic_expr = match t with
  | ITac.TacIntroPattern(a,b)         -> Tacexpr.TacIntroPattern(a,b)
  | ITac.TacApply (a,b,c,d)           -> Tacexpr.TacApply (a,b,c,d)
  | ITac.TacElim (a,b,c)              -> Tacexpr.TacElim (a,b,c)
  | ITac.TacCase (a,b)                -> Tacexpr.TacCase (a,b)
  | ITac.TacMutualFix (a,b,c)         -> Tacexpr.TacMutualFix (a,b,c)
  | ITac.TacMutualCofix (a,b)         -> Tacexpr.TacMutualCofix (a,b)
  | ITac.TacAssert (a,b,c,d)          -> Tacexpr.TacAssert (a,b,c,d)
  | ITac.TacGeneralize a              -> Tacexpr.TacGeneralize a
  | ITac.TacLetTac (a,b,c,d,e)        -> Tacexpr.TacLetTac (a,b,c,d,e)
  | ITac.TacInductionDestruct (a,b,c) -> Tacexpr.TacInductionDestruct (a,b,c)
  | ITac.TacReduce (a,b)              -> Tacexpr.TacReduce (a,b)
  | ITac.TacChange (a,b,c)            -> Tacexpr.TacChange (a,b,c)
  | ITac.TacRewrite (a,b,c,d)         -> Tacexpr.TacRewrite (a,b,c,d)
  | ITac.TacInversion (a,b)           -> Tacexpr.TacInversion (a,b)
and _gen_tactic_arg_get (t : ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_arg) :
  'a Tacexpr.gen_tactic_arg = match t with
  | ITac.TacGeneric a      -> Tacexpr.TacGeneric a
  | ITac.ConstrMayEval a   -> Tacexpr.ConstrMayEval a
  | ITac.Reference a       -> Tacexpr.Reference a
  | ITac.TacCall (a,b,c)   -> Tacexpr.TacCall (a,b, List.map _gen_tactic_arg_get c)
  | ITac.TacFreshId a      -> Tacexpr.TacFreshId a
  | ITac.Tacexp a          -> Tacexpr.Tacexp a
  | ITac.TacPretype a      -> Tacexpr.TacPretype a
  | ITac.TacNumgoals       -> Tacexpr.TacNumgoals
and _gen_tactic_expr_get (t : ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_expr) :
  'a Tacexpr.gen_tactic_expr =
  let u  x = _gen_tactic_expr_get x in
  let uu x = List.map u x           in
  let ua x = Array.map u x          in
  match t with
  | ITac.TacAtom (a,b)            -> Tacexpr.TacAtom (a,_gen_atom_tactic_expr_get b)
  | ITac.TacThen (a,b)            -> Tacexpr.TacThen (u a, u b)
  | ITac.TacDispatch a            -> Tacexpr.TacDispatch (uu a)
  | ITac.TacExtendTac (a,b,c)     -> Tacexpr.TacExtendTac (ua a, u b, ua c)
  | ITac.TacThens (a,b)           -> Tacexpr.TacThens (u a, uu b)
  | ITac.TacThens3parts (a,b,c,d) -> Tacexpr.TacThens3parts (u a, ua b, u c, ua d)
  | ITac.TacFirst a               -> Tacexpr.TacFirst (uu a)
  | ITac.TacComplete a            -> Tacexpr.TacComplete (u a)
  | ITac.TacSolve a               -> Tacexpr.TacSolve (uu a)
  | ITac.TacTry a                 -> Tacexpr.TacTry (u a)
  | ITac.TacOr (a,b)              -> Tacexpr.TacOr (u a, u b)
  | ITac.TacOnce a                -> Tacexpr.TacOnce (u a)
  | ITac.TacExactlyOnce a         -> Tacexpr.TacExactlyOnce (u a)
  | ITac.TacIfThenCatch (a,b,c)   -> Tacexpr.TacIfThenCatch (u a,u b,u c)
  | ITac.TacOrelse (a,b)          -> Tacexpr.TacOrelse (u a,u b)
  | ITac.TacDo (a,b)              -> Tacexpr.TacDo (a,u b)
  | ITac.TacTimeout (a,b)         -> Tacexpr.TacTimeout (a,u b)
  | ITac.TacTime (a,b)            -> Tacexpr.TacTime (a,u b)
  | ITac.TacRepeat a              -> Tacexpr.TacRepeat (u a)
  | ITac.TacProgress a            -> Tacexpr.TacProgress (u a)
  | ITac.TacShowHyps a            -> Tacexpr.TacShowHyps (u a)
  | ITac.TacAbstract (a,b)        -> Tacexpr.TacAbstract (u a,b)
  | ITac.TacId a                  -> Tacexpr.TacId a
  | ITac.TacFail (a,b,c)          -> Tacexpr.TacFail (a,b,c)
  | ITac.TacInfo a                -> Tacexpr.TacInfo (u a)
  | ITac.TacLetIn (a, l, t)       ->
    let _pt = List.map (fun (a,t) -> (a,_gen_tactic_arg_get t)) in
    Tacexpr.TacLetIn (a, _pt l, _gen_tactic_expr_get t)
  | ITac.TacMatch (a,e,mr)          ->
    let _gmr = List.map (function
        | Tacexpr.Pat (a,b,t) -> Tacexpr.Pat (a,b,_gen_tactic_expr_get t)
        | Tacexpr.All e       -> Tacexpr.All (_gen_tactic_expr_get e)
      ) in
    Tacexpr.TacMatch(a, _gen_tactic_expr_get e, _gmr mr)
  | ITac.TacMatchGoal (a,d,t)     ->
    let _gmr = List.map (function
        | Tacexpr.Pat (a,b,t) -> Tacexpr.Pat (a,b,_gen_tactic_expr_get t)
        | Tacexpr.All e       -> Tacexpr.All (_gen_tactic_expr_get e)
      ) in
    Tacexpr.TacMatchGoal(a,d, _gmr t)
  | ITac.TacFun a                 -> Tacexpr.TacFun (_gen_tactic_fun_ast_get a)
  | ITac.TacArg (l,a)             -> Tacexpr.TacArg (l, _gen_tactic_arg_get a)
  | ITac.TacSelect(gs,te)         -> Tacexpr.TacSelect(gs, _gen_tactic_expr_get te)
  | ITac.TacML (a,b,c)            -> Tacexpr.TacML (a,b,List.map _gen_tactic_arg_get c)
  | ITac.TacAlias (a,b,c)         -> Tacexpr.TacAlias (a,b,List.map _gen_tactic_arg_get c)
and _gen_tactic_fun_ast_get (t : ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_fun_ast) :
  'a Tacexpr.gen_tactic_fun_ast =
  match t with
  | (a,b) -> (a, _gen_tactic_expr_get b)

type 'd gen_atomic_tactic_expr = 'd Tacexpr.gen_atomic_tactic_expr

let sexp_of_gen_atomic_tactic_expr
  t d p c r n te l (tac : 'a Tacexpr.gen_atomic_tactic_expr) : Sexp.t =
  ITac.sexp_of_gen_atomic_tactic_expr t d p c r n te l (_gen_atom_tactic_expr_put tac)

let sexp_of_gen_tactic_expr
  t d p c r n te l (tac : 'a Tacexpr.gen_tactic_expr) : Sexp.t =
  ITac.sexp_of_gen_tactic_expr t d p c r n te l (_gen_tactic_expr_put tac)

let sexp_of_gen_tactic_arg
  t d p c r n te l (tac : 'a Tacexpr.gen_tactic_arg) : Sexp.t =
  ITac.sexp_of_gen_tactic_arg t d p c r n te l (_gen_tactic_arg_put tac)

let sexp_of_gen_fun_ast
  t d p c r n te l (tac : 'a Tacexpr.gen_tactic_fun_ast) : Sexp.t =
  ITac.sexp_of_gen_tactic_fun_ast t d p c r n te l (_gen_tactic_fun_ast_put tac)

let gen_atomic_tactic_expr_of_sexp (tac : Sexp.t)
  t d p c r n te l : 'a Tacexpr.gen_atomic_tactic_expr =
  _gen_atom_tactic_expr_get (ITac.gen_atomic_tactic_expr_of_sexp t d p c r n te l tac)

let gen_tactic_expr_of_sexp (tac : Sexp.t)
  t d p c r n te l : 'a Tacexpr.gen_tactic_expr =
  _gen_tactic_expr_get (ITac.gen_tactic_expr_of_sexp t d p c r n te l tac)

let gen_tactic_arg_of_sexp (tac : Sexp.t)
  t d p c r n te l : 'a Tacexpr.gen_tactic_arg =
  _gen_tactic_arg_get (ITac.gen_tactic_arg_of_sexp t d p c r n te l tac)

let gen_fun_ast_of_sexp (tac : Sexp.t)
  t d p c r n te l : 'a Tacexpr.gen_tactic_fun_ast =
  _gen_tactic_fun_ast_get (ITac.gen_tactic_fun_ast_of_sexp t d p c r n te l tac)

(************************************************************************)
(* Main tactics types, we follow tacexpr and provide glob,raw, and      *)
(* atomic                                                               *)
(************************************************************************)

(* Glob *)
type glob_constr_and_expr =
  [%import: Tacexpr.glob_constr_and_expr
  [@with
     Glob_term.glob_constr  := glob_constr;
     Constrexpr.constr_expr := constr_expr;
  ]]
  [@@deriving sexp]

type binding_bound_vars =
  [%import: Tacexpr.binding_bound_vars
  [@with
     Names.Id.Set.t := id_set;
  ]]
  [@@deriving sexp]

type glob_constr_pattern_and_expr =
  [%import: Tacexpr.glob_constr_pattern_and_expr
  [@with
     Glob_term.glob_constr  := glob_constr;
     Constrexpr.constr_expr := constr_expr;
     Pattern.constr_pattern := constr_pattern;
  ]]
  [@@deriving sexp]

type glob_tactic_expr = Tacexpr.glob_tactic_expr
type glob_atomic_tactic_expr = Tacexpr.glob_atomic_tactic_expr

let rec glob_tactic_expr_of_sexp tac =
  gen_tactic_expr_of_sexp
    tac
    glob_constr_and_expr_of_sexp
    glob_constr_and_expr_of_sexp
    glob_constr_pattern_and_expr_of_sexp
    (or_var_of_sexp (and_short_name_of_sexp evaluable_global_reference_of_sexp))
    (or_var_of_sexp (located_of_sexp ltac_constant_of_sexp))
    (located_of_sexp id_of_sexp)
    glob_tactic_expr_of_sexp
    glevel_of_sexp
and glob_atomic_tactic_expr_of_sexp tac =
  gen_atomic_tactic_expr_of_sexp
    tac
    glob_constr_and_expr_of_sexp
    glob_constr_and_expr_of_sexp
    glob_constr_pattern_and_expr_of_sexp
    (or_var_of_sexp (and_short_name_of_sexp evaluable_global_reference_of_sexp))
    (or_var_of_sexp (located_of_sexp ltac_constant_of_sexp))
    (located_of_sexp id_of_sexp)
    glob_tactic_expr_of_sexp
    glevel_of_sexp

let rec sexp_of_glob_tactic_expr (tac : glob_tactic_expr) =
  sexp_of_gen_tactic_expr
    sexp_of_glob_constr_and_expr
    sexp_of_glob_constr_and_expr
    sexp_of_glob_constr_pattern_and_expr
    (sexp_of_or_var (sexp_of_and_short_name sexp_of_evaluable_global_reference))
    (sexp_of_or_var (sexp_of_located sexp_of_ltac_constant))
    (sexp_of_located sexp_of_id)
    sexp_of_glob_tactic_expr
    sexp_of_glevel
    tac
and sexp_of_glob_atomic_tactic_expr (tac : glob_atomic_tactic_expr) =
  sexp_of_gen_atomic_tactic_expr
    sexp_of_glob_constr_and_expr
    sexp_of_glob_constr_and_expr
    sexp_of_glob_constr_pattern_and_expr
    (sexp_of_or_var (sexp_of_and_short_name sexp_of_evaluable_global_reference))
    (sexp_of_or_var (sexp_of_located sexp_of_ltac_constant))
    (sexp_of_located sexp_of_id)
    sexp_of_glob_tactic_expr
    sexp_of_glevel
    tac

(* Raw *)
type raw_tactic_expr = Tacexpr.raw_tactic_expr
type raw_atomic_tactic_expr = Tacexpr.raw_atomic_tactic_expr

type u = loc * id
  [@@deriving sexp]

let rec raw_tactic_expr_of_sexp tac =
  gen_tactic_expr_of_sexp
    tac
    constr_expr_of_sexp
    constr_expr_of_sexp
    constr_pattern_expr_of_sexp
    (or_by_notation_of_sexp reference_of_sexp)
    reference_of_sexp
    u_of_sexp
    raw_tactic_expr_of_sexp
    rlevel_of_sexp
and raw_atomic_tactic_expr_of_sexp tac =
  gen_atomic_tactic_expr_of_sexp
    tac
    constr_expr_of_sexp
    constr_expr_of_sexp
    constr_pattern_expr_of_sexp
    (or_by_notation_of_sexp reference_of_sexp)
    reference_of_sexp
    u_of_sexp
    raw_tactic_expr_of_sexp
    rlevel_of_sexp

let rec sexp_of_raw_tactic_expr (tac : raw_tactic_expr) =
  sexp_of_gen_tactic_expr
    sexp_of_constr_expr
    sexp_of_constr_expr
    sexp_of_constr_pattern_expr
    (sexp_of_or_by_notation sexp_of_reference)
    sexp_of_reference
    sexp_of_u
    sexp_of_raw_tactic_expr
    sexp_of_rlevel
    tac
and sexp_of_raw_atomic_tactic_expr tac =
  sexp_of_gen_atomic_tactic_expr
    sexp_of_constr_expr
    sexp_of_constr_expr
    sexp_of_constr_pattern_expr
    (sexp_of_or_by_notation sexp_of_reference)
    sexp_of_reference
    sexp_of_u
    sexp_of_raw_tactic_expr
    sexp_of_rlevel
    tac

(* Atomic *)
type atomic_tactic_expr = Tacexpr.atomic_tactic_expr

let atomic_tactic_expr_of_sexp tac =
  gen_atomic_tactic_expr_of_sexp tac
    constr_of_sexp
    glob_constr_and_expr_of_sexp
    constr_pattern_of_sexp
    evaluable_global_reference_of_sexp
    (located_of_sexp ltac_constant_of_sexp)
    id_of_sexp
    unit_of_sexp
    tlevel_of_sexp

let sexp_of_atomic_tactic_expr tac =
  sexp_of_gen_atomic_tactic_expr
    sexp_of_constr
    sexp_of_glob_constr_and_expr
    sexp_of_constr_pattern
    sexp_of_evaluable_global_reference
    (sexp_of_located sexp_of_ltac_constant)
    sexp_of_id
    sexp_of_unit
    sexp_of_tlevel
    tac

(* Helpers for raw_red_expr *)
type r_trm =
  [%import: Tacexpr.r_trm
  [@with
     Constrexpr.constr_expr := constr_expr;
  ]]
  [@@deriving sexp]

type r_cst =
  [%import: Tacexpr.r_cst
  [@with
    Libnames.reference := reference;
    Misctypes.or_by_notation := or_by_notation;
  ]]
  [@@deriving sexp]

type r_pat =
  [%import: Tacexpr.r_pat
  [@with
     Constrexpr.constr_expr := constr_expr;
     Constrexpr.constr_pattern_expr := constr_pattern_expr;
  ]]
  [@@deriving sexp]

type raw_red_expr =
  [%import: Tacexpr.raw_red_expr
  [@with
     Genredexpr.red_expr_gen := red_expr_gen;
  ]]
  [@@deriving sexp]

