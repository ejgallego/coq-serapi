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

open Sexplib.Conv

let exn_of_sexp _ = Obj.magic 0

open Ser_loc
open Ser_flags
open Ser_goptions
open Ser_names
open Ser_misctypes
open Ser_univ
open Ser_conv_oracle
open Ser_decl_kinds
open Ser_genarg
open Ser_libnames
open Ser_extend
open Ser_stateid
open Ser_constrexpr
open Ser_tacexpr

type lident     = [%import: Vernacexpr.lident
    [@with Loc.t        := loc;
           Loc.located  := located;
           Names.Id.t := id;
    ]]
  [@@deriving sexp]

type lname      = [%import: Vernacexpr.lname
    [@with Loc.t        := loc;
           Loc.located  := located;
           Names.Name.t := name;
    ]]
  [@@deriving sexp]

type lstring    = [%import: Vernacexpr.lstring
    [@with Loc.t        := loc;
           Loc.located  := located;
           Names.Name.t := name;
           Names.Id.t := id;
    ]]
  [@@deriving sexp]

(* type lreference = [%import: Vernacexpr.lreference *)
(*      [@with Names.Id.t := id; *)
(*             Libnames.reference := reference; *)
(*      ]] *)
(*   [@@deriving sexp] *)

type class_rawexpr = [%import: Vernacexpr.class_rawexpr
     [@with Libnames.reference := reference;
            Misctypes.or_by_notation := or_by_notation;
     ]]
  [@@deriving sexp]

type goal_identifier = [%import: Vernacexpr.goal_identifier]
  [@@deriving sexp]
type scope_name      = [%import: Vernacexpr.scope_name]
  [@@deriving sexp]

type goal_selector = [%import: Vernacexpr.goal_selector
     [@with Names.Id.t := id;
     ]]
  [@@deriving sexp]

type goal_reference = [%import: Vernacexpr.goal_reference
     [@with Names.Id.t := id;
     ]]
  [@@deriving sexp]

type printable = [%import: Vernacexpr.printable
     [@with Names.Id.t := id;
            Libnames.reference   := reference;

            Misctypes.or_by_notation := or_by_notation;

            Names.Id.t   := id;
            Names.Name.t := name;
            Names.DirPath.t := dirpath;
     ]]
  [@@deriving sexp]

type search_about_item = [%import: Vernacexpr.search_about_item
     [@with Names.Id.t := id;
            Constrexpr.constr_pattern_expr := constr_pattern_expr;
     ]]
  [@@deriving sexp]

type searchable =  [%import: Vernacexpr.searchable
     [@with Names.Id.t := id;
            Constrexpr.constr_pattern_expr := constr_pattern_expr;
     ]]
  [@@deriving sexp]

type locatable = [%import: Vernacexpr.locatable
     [@with Names.Id.t := id;
            Misctypes.or_by_notation := or_by_notation;
            Libnames.reference := reference;
     ]]
  [@@deriving sexp]

type showable =  [%import: Vernacexpr.showable
     [@with Names.Id.t := id;
            Libnames.reference := reference;
     ]]
  [@@deriving sexp]

type comment =  [%import: Vernacexpr.comment
     [@with Names.Id.t := id;
            Constrexpr.constr_expr := constr_expr;
     ]]
  [@@deriving sexp]

type reference_or_constr =  [%import: Vernacexpr.reference_or_constr
     [@with Names.Id.t := id;
            Libnames.reference := reference;
            Constrexpr.constr_expr := constr_expr;
     ]]
  [@@deriving sexp]

type hint_mode =
  [%import: Vernacexpr.hint_mode]
  [@@deriving sexp]

type hints_expr =  [%import: Vernacexpr.hints_expr
     [@with Names.Id.t := id;
            Libnames.reference := reference;
            Constrexpr.constr_expr := constr_expr;
            Tacexpr.raw_tactic_expr := raw_tactic_expr;
     ]]
  [@@deriving sexp]

type search_restriction =  [%import: Vernacexpr.search_restriction
     [@with Names.Id.t := id;
            Libnames.reference := reference;
     ]]
  [@@deriving sexp]


type rec_flag          = [%import: Vernacexpr.rec_flag          ] [@@deriving sexp]
type verbose_flag      = [%import: Vernacexpr.verbose_flag      ] [@@deriving sexp]
type opacity_flag      = [%import: Vernacexpr.opacity_flag      ] [@@deriving sexp]
type coercion_flag     = [%import: Vernacexpr.coercion_flag     ] [@@deriving sexp]
type inductive_flag    = [%import: Vernacexpr.inductive_flag
     [@with Decl_kinds.recursivity_kind := recursivity_kind;
     ]]
  [@@deriving sexp]
type instance_flag     = [%import: Vernacexpr.instance_flag     ] [@@deriving sexp]
type export_flag       = [%import: Vernacexpr.export_flag       ] [@@deriving sexp]
type onlyparsing_flag  = [%import: Vernacexpr.onlyparsing_flag
     [@with Flags.compat_version := compat_version;
     ]]
  [@@deriving sexp]

type locality_flag     = [%import: Vernacexpr.locality_flag     ] [@@deriving sexp]
type obsolete_locality = [%import: Vernacexpr.obsolete_locality ] [@@deriving sexp]


type option_value =
  [%import: Vernacexpr.option_value
  ]
  [@@deriving sexp]

type option_ref_value =
  [%import: Vernacexpr.option_ref_value
  [@with
    Libnames.reference := reference;
  ]]
  [@@deriving sexp]

type plident =
  [%import: Vernacexpr.plident ]
  [@@deriving sexp]

type sort_expr =
  [%import: Vernacexpr.sort_expr
  [@with Misctypes.glob_sort := glob_sort;
  ]]
  [@@deriving sexp]

type definition_expr =
  [%import: Vernacexpr.definition_expr
  [@with
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Tacexpr.raw_red_expr := raw_red_expr;
  ]]
  [@@deriving sexp]

type fixpoint_expr =
  [%import: Vernacexpr.fixpoint_expr
  [@with
    Loc.t        := loc;
    Loc.located  := located;
    Names.Id.t := id;
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
  ]]
  [@@deriving sexp]

type cofixpoint_expr =
  [%import: Vernacexpr.cofixpoint_expr
  [@with
    Loc.t        := loc;
    Loc.located  := located;
    Names.Id.t := id;
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
  ]]
  [@@deriving sexp]

type local_decl_expr =
  [%import: Vernacexpr.local_decl_expr
  [@with
    Loc.t        := loc;
    Loc.located  := located;
    Names.Id.t := id;
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
  ]]
  [@@deriving sexp]

type inductive_kind =
  [%import: Vernacexpr.inductive_kind
  [@with
    Loc.t        := loc;
    Loc.located  := located;
    Names.Id.t := id;
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
  ]]
  [@@deriving sexp]

type decl_notation =
  [%import: Vernacexpr.decl_notation
  [@with
    Loc.t        := loc;
    Loc.located  := located;
    Names.Id.t := id;
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
  ]]
  [@@deriving sexp]

type simple_binder =
  [%import: Vernacexpr.simple_binder
  [@with
    Loc.t        := loc;
    Loc.located  := located;
    Names.Id.t := id;
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
  ]]
  [@@deriving sexp]

type class_binder =
  [%import: Vernacexpr.class_binder
  [@with
    Loc.t        := loc;
    Loc.located  := located;
    Names.Id.t := id;
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
  ]]
  [@@deriving sexp]

type 'a with_coercion =
  [%import: 'a Vernacexpr.with_coercion
  (* [@with *)
  (* ]] *)
  ]
  [@@deriving sexp]

type 'a with_instance =
  [%import: 'a Vernacexpr.with_instance
  (* [@with *)
  (* ]] *)
  ]
  [@@deriving sexp]

type 'a with_notation =
  [%import: 'a Vernacexpr.with_notation
  [@with
    Loc.t        := loc;
  ]]
  [@@deriving sexp]

type 'a with_priority =
  [%import: 'a Vernacexpr.with_priority
  (* [@with *)
  (* ]] *)
  ]
  [@@deriving sexp]

type constructor_expr =
  [%import: Vernacexpr.constructor_expr
  [@with
    Loc.t        := loc;
    Loc.located  := located;
    Names.Id.t := id;
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
  ]]
  [@@deriving sexp]

type constructor_list_or_record_decl_expr =
  [%import: Vernacexpr.constructor_list_or_record_decl_expr
  (* [@with *)
  (* ]] *)
  ]
  [@@deriving sexp]

type inductive_expr =
  [%import: Vernacexpr.inductive_expr
  [@with
    Loc.t        := loc;
    Loc.located  := located;
    Names.Id.t := id;
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
  ]]
  [@@deriving sexp]

type one_inductive_expr =
  [%import: Vernacexpr.one_inductive_expr
  [@with
    Loc.t        := loc;
    Loc.located  := located;
    Names.Id.t := id;
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
  ]]
  [@@deriving sexp]

type proof_expr =
  [%import: Vernacexpr.proof_expr
  [@with
    Constrexpr.local_binder := local_binder;
    Constrexpr.constr_expr  := constr_expr;
    Constrexpr.recursion_order_expr := recursion_order_expr;
    Tacexpr.raw_red_expr := raw_red_expr;
  ]]
  [@@deriving sexp]

(* type grammar_tactic_prod_item_expr = *)
(*   [%import: Vernacexpr.grammar_tactic_prod_item_expr *)
(*   [@with Loc.t        := loc; *)
(*          Loc.located  := located; *)
(*          Names.Id.t := id; *)
(*          Tacexpr.raw_tactic_expr := raw_tactic_expr; *)
(*   ]] *)
(*   [@@deriving sexp] *)

type syntax_modifier =
  [%import: Vernacexpr.syntax_modifier
  [@with Loc.t        := loc;
         Loc.located  := located;

         Names.Id.t   := id;

         Flags.compat_version    := compat_version;

         Extend.production_level := production_level;
         Extend.gram_assoc       := gram_assoc;
         Extend.simple_constr_prod_entry_key := simple_constr_prod_entry_key;
  ]]
  [@@deriving sexp]

type proof_end =
  [%import: Vernacexpr.proof_end
  [@with
    Loc.t        := loc;
    Decl_kinds.theorem_kind := theorem_kind;
  ]]
  [@@deriving sexp]

type scheme =
  [%import: Vernacexpr.scheme
  [@with
    Loc.t        := loc;
    Libnames.reference := reference;
    Misctypes.or_by_notation := or_by_notation;
  ]]
  [@@deriving sexp]

type section_subset_expr =
  [%import: Vernacexpr.section_subset_expr
  [@with
    Loc.t        := loc;
    Misctypes.or_by_notation := or_by_notation;
  ]]
  [@@deriving sexp]

type extend_name =
  [%import: Vernacexpr.extend_name]
  [@@deriving sexp]

type register_kind =
  [%import: Vernacexpr.register_kind
  [@with
    Loc.t        := loc;
  ]]
  [@@deriving sexp]

type bullet =
  [%import: Vernacexpr.bullet
  [@with
    Loc.t        := loc;
  ]]
  [@@deriving sexp]

type 'a stm_vernac =
  [%import: 'a Vernacexpr.stm_vernac
  [@with
    Loc.t        := loc;
    Stateid.t    := stateid;
  ]]
  [@@deriving sexp]

type 'a module_signature =
  [%import: 'a Vernacexpr.module_signature
  [@with
    Loc.t        := loc;
  ]]
  [@@deriving sexp]

type inline =
  [%import: Vernacexpr.inline
  [@with
    Loc.t        := loc;
    Libnames.reference := reference;
    Misctypes.or_by_notation := or_by_notation;
  ]]
  [@@deriving sexp]

type module_ast_inl =
  [%import: Vernacexpr.module_ast_inl
  [@with
    Loc.t        := loc;
    Libnames.reference := reference;
    Misctypes.or_by_notation := or_by_notation;
    Constrexpr.module_ast := module_ast;
  ]]
  [@@deriving sexp]

type module_binder =
  [%import: Vernacexpr.module_binder
  [@with
    Loc.t        := loc;
    Libnames.reference := reference;
    Misctypes.or_by_notation := or_by_notation;
  ]]
  [@@deriving sexp]


type vernac_expr =
  [%import: Vernacexpr.vernac_expr
  [@with
    Loc.t        := loc;
    Loc.located  := located;

    Names.Id.t      := id;
    Names.Name.t    := name;
    Names.DirPath.t := dirpath;

    Decl_kinds.locality         := locality;
    Decl_kinds.recursivity_kind := recursivity_kind;
    Decl_kinds.definition_object_kind := definition_object_kind;
    Decl_kinds.theorem_kind := theorem_kind;
    Decl_kinds.assumption_object_kind := assumption_object_kind;
    Decl_kinds.private_flag           := private_flag;

    Goptions.option_name := option_name;

    Genarg.raw_generic_argument := raw_generic_argument;

    Misctypes.or_by_notation := or_by_notation;
    Libnames.reference := reference;

    Constrexpr.constr_expr := constr_expr;
    Constrexpr.explicitation := explicitation;
    Constrexpr.local_binder := local_binder;
    Constrexpr.typeclass_constraint := typeclass_constraint;

    Tacexpr.raw_tactic_expr := raw_tactic_expr;
    Tacexpr.raw_red_expr    := raw_red_expr;

    Conv_oracle.level   := conv_level;
    Univ.constraint_type    := constraint_type;
    ]]
  [@@deriving sexp]

(* and vernac_list = *)
(*   [%import: Vernacexpr.vernac_list] *)

(* and located_vernac_expr = *)
(*   [%import: Vernacexpr.located_vernac_expr *)
(*   [@with *)
(*     Loc.t        := loc; *)
(*     Loc.located  := located; *)
(*   ]] *)
(*   [@@deriving sexp] *)

(* We need to overload the printing for the Extend mechanism... *)
let sexp_of_vernac_expr vrc = match vrc with
  | VernacExtend (s, cl)->
    let open Sexplib in
    begin try
      let rl = Egramml.get_extend_vernac_rule s in
      let pr_str s = Sexp.(List [Atom "NT"; Atom s])       in
      let pr_arg a =
        let sa = Pptactic.pr_raw_generic (Global.env ()) a in
        Sexp.(List [Atom "NT"; Atom (Pp.string_of_ppcmds sa)])
      in
      let rec aux rl cl =
        match rl, cl with
        | Egramml.GramNonTerminal _ :: rl, arg :: cl -> pr_arg arg :: aux rl cl
        | Egramml.GramTerminal    s :: rl, cl        -> pr_str s   :: aux rl cl
        | [], [] -> []
        | _ -> assert false in
      Sexp.(List [Atom "VernacExtend"; List [Atom (fst s); List (aux rl cl)]])
    with Not_found ->
      Sexp.(List [Atom "VernacExtend"; List [Atom (fst s); Atom " not assigned!"]])
    end
  | _ -> sexp_of_vernac_expr vrc

