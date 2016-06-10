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

(* Options for the toplevel *)
type ser_opts = {
  coqlib   : string option;       (* Whether we should load the prelude, and its location *)
  in_chan  : in_channel;          (* Input/Output channels                                *)
  out_chan : out_channel;
  human    : bool;
  print0   : bool;
}

(** [ser_loop opts] main se(xp)r-protocol loop *)
val ser_loop : ser_opts -> unit

(** We provide the public API for ocaml client's  *)
open Sexplib

type control_cmd =
    StmState
  | StmAdd     of Stateid.t * string
  | StmQuery   of Stateid.t * string
  | StmEditAt  of Stateid.t
  | StmObserve of Stateid.t
  | SetOpt     of unit
  | LibAdd     of string list * string * bool
  | Quit

val sexp_of_control_cmd : control_cmd -> Sexp.t
val control_cmd_of_sexp : Sexp.t -> control_cmd

type pp_opt =
  | PpSexp
  | PpStr

val pp_opt_of_sexp : Sexp.t -> pp_opt
val sexp_of_pp_opt : pp_opt -> Sexp.t

type query_limit = int option
val query_limit_of_sexp : Sexp.t -> query_limit
val sexp_of_query_limit : query_limit -> Sexp.t

type query_opt = query_limit * pp_opt
val query_opt_of_sexp : Sexp.t -> query_opt
val sexp_of_query_opt : query_opt -> Sexp.t

(** We would ideally make both query_cmd and coq_object depend on a
  * tag such that query : 'a query -> 'a coq_object.
  *)
type query_cmd =
  | Option of string
  | Search of string
  | Goals

val query_cmd_of_sexp : Sexp.t -> query_cmd
val sexp_of_query_cmd : query_cmd -> Sexp.t

type coq_object =
    CoqString  of string
  | CoqRichpp  of Richpp.richpp
  | CoqRichXml of Richpp.richpp
  | CoqOption  of Goptions.option_state
  | CoqConstr  of Constr.constr
  | CoqExpr    of Constrexpr.constr_expr
  | CoqGoal    of (Constr.constr * (Names.Id.t list * Constr.constr option * Constr.constr) list) Proof.pre_goals

val coq_object_of_sexp : Sexp.t -> coq_object
val sexp_of_coq_object : coq_object -> Sexp.t

type answer_kind =
    Ack
  | StmInfo of Stateid.t * [`NewTip | `Unfocus of Stateid.t | `Focus of Stm.focus] option
  | ObjList of coq_object list
  | CoqExn  of exn

val sexp_of_answer_kind : answer_kind -> Sexp.t
val answer_kind_of_sexp : Sexp.t -> answer_kind

type cmd =
    Control of control_cmd
  | Query   of query_opt * query_cmd
  | Print   of coq_object
  | Parse   of string
  | Help

val cmd_of_sexp : Sexp.t -> cmd
val sexp_of_cmd : cmd -> Sexp.t

type answer =
    Answer    of int * answer_kind
  | Feedback  of Feedback.feedback
  | SexpError of Sexp.t

val sexp_of_answer : answer -> Sexp.t
val answer_of_sexp : Sexp.t -> answer
