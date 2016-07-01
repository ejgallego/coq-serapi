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

(******************************************************************************)
(* We provide the public API here for Ocaml clients                           *)
(******************************************************************************)

open Sexplib.Conv

(******************************************************************************)
(* Basic Protocol Objects                                                     *)
(******************************************************************************)
type coq_object =
    CoqString   of string
  | CoqSList    of string list
  | CoqRichpp   of Richpp.richpp
  | CoqRichXml  of Richpp.richpp
  | CoqLoc      of Loc.t
  | CoqOption   of Goptions.option_name * Goptions.option_state
  | CoqConstr   of Constr.constr
  | CoqExpr     of Constrexpr.constr_expr
  | CoqTactic   of Names.KerName.t * Tacenv.ltac_entry
  | CoqQualId   of Libnames.qualid
  | CoqGlobRef  of Globnames.global_reference
  | CoqImplicit of Impargs.implicits_list
  | CoqProfData of Profile_ltac.ltacprof_results
  (* | CoqPhyLoc  of Library.library_location * Names.DirPath.t * string (\* CUnix.physical_path *\) *)
  | CoqGoal     of (Constr.constr * (Names.Id.t list * Constr.constr option * Constr.constr) list) Proof.pre_goals

(******************************************************************************)
(* Printing Sub-Protocol                                                      *)
(******************************************************************************)

(** Query output format  *)
type print_format =
  | PpSer
  | PpStr

type print_opt = {
  pp_format : print_format  [@default PpStr];
  pp_depth  : int           [@default 0];
  pp_elide  : string        [@default "..."];
  (* pp_margin : int; *)
}

(******************************************************************************)
(* Parsing Sub-Protocol                                                       *)
(******************************************************************************)

(* no public interface *)

(******************************************************************************)
(* Answer Types                                                               *)
(******************************************************************************)

exception NoSuchState of Stateid.t

type answer_kind =
    Ack
  | StmCurId     of Stateid.t
  | StmAdded     of Stateid.t * Loc.t * [`NewTip | `Unfocus of Stateid.t ]
  | StmCanceled  of Stateid.t list
  | StmEdited    of                     [`NewTip | `Focus   of Stm.focus ]
  | ObjList      of coq_object list
  | CoqExn       of exn
  | Completed

(******************************************************************************)
(* Control Sub-Protocol                                                       *)
(******************************************************************************)

type add_opts = {
  lim    : int       sexp_option;
  ontop  : Stateid.t sexp_option;
  newtip : Stateid.t sexp_option;
  verb   : bool      [@default false];
}

type control_cmd =
    StmState
  | StmAdd     of       add_opts  * string      (* Stm.add       *)
  | StmQuery   of       Stateid.t * string
  | StmCancel  of       Stateid.t list
  | StmEditAt  of       Stateid.t
  | StmObserve of       Stateid.t
  | StmJoin                                     (* Stm.join      *)
  | StmStopWorker of    string
  | SetOpt     of bool option * Goptions.option_name * Goptions.option_value
  | LibAdd     of string list * string * bool
  | Quit

(******************************************************************************)
(* Query Sub-Protocol                                                         *)
(******************************************************************************)

type query_pred =
  | Prefix of string

type query_opt =
  { preds : query_pred sexp_list;
    limit : int sexp_option;
    sid   : Stateid.t [@default Stm.get_current_state()];
    pp    : print_opt [@default { pp_format = PpSer ; pp_depth = 0; pp_elide = "..." } ];
  }

(** We would ideally make both query_cmd and coq_object depend on a
  * tag such that query : 'a query -> 'a coq_object.
  *)
type query_cmd =
  | Option
  | Search
  | Goals     of Stateid.t        (* Return goals [TODO: Add filtering/limiting options] *)
  | TypeOf    of string           (* XXX Unimplemented *)
  | Names     of string           (* argument is prefix -> XXX Move to use the prefix predicate *)
  | Tactics   of string           (* argument is prefix -> XXX Move to use the prefix predicate *)
  | Locate    of string           (* argument is prefix -> XXX Move to use the prefix predicate *)
  | Implicits of string           (* XXX Print LTAC signatures (with prefix) *)
  | ProfileData

(******************************************************************************)
(* Help                                                                       *)
(******************************************************************************)

(* no public interface *)

(******************************************************************************)
(* Top-Level Commands                                                         *)
(******************************************************************************)

type cmd =
    Control of control_cmd
  | Print   of print_opt * coq_object
  | Parse   of int * string
  | Query   of query_opt * query_cmd
  | Noop
  | Help

val exec_cmd : cmd -> answer_kind list

type cmd_tag = string
type tagged_cmd = cmd_tag * cmd

(* XXX: Maybe 'a answer for a parametric serializer? *)
type answer =
  | Answer    of cmd_tag * answer_kind
  | Feedback  of Feedback.feedback

(******************************************************************************)
(* Global Protocol Options                                                    *)
(******************************************************************************)

(* type ser_opts = { *)
  (* coqlib   : string option;       (\* Whether we should load the prelude, and its location *\) *)
  (* in_chan  : in_channel;          (\* Input/Output channels                                *\) *)
  (* out_chan : out_channel; *)
  (* human    : bool; *)
  (* print0   : bool; *)
  (* lheader  : bool; *)
  (* implicit : bool; *)
(*   async    : Sertop_init.async_flags; *)
(* } *)

