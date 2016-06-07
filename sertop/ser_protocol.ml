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

open Ser_feedback
open Ser_constr
open Ser_glob_term

(* New protocol plus interpreter *)

type control_cmd =
  | StmAdd     of unit
  | StmEdit    of unit
  | StmObserve of unit
  | StmState   of unit
  | Quit       of unit
  | SetOpt     of unit
  [@@deriving sexp]

(* We'd like to use GADT here, but deriving sexp doesn't support them, we will
   need to delay this for now.
*)
(* See https://github.com/c-cube/cconv to see if we could fix that *)
(* type _ query_cmd = *)
(*   | Option : string query_cmd *)
(*   | Search : string query_cmd *)
(*   | Goals  : unit -> int query_cmd *)
(*   [@@deriving sexp] *)

type query_opt =
  | Summary                     (* Number of objects matched                 *)
  | PpResults                   (* Return results printed                    *)
  | RawResults                  (* Return results in (serialized) raw format *)
  [@@deriving sexp]

type query_cmd =
  | Option of string
  | Search of string option
  | Goals                       (* Add filtering *)
  [@@deriving sexp]

type coq_object =
  | CoqConstr of constr
  | CoqGlob   of glob_constr
  [@@deriving sexp]

type cmd =
  | Control of control_cmd
  | Query   of query_opt * query_cmd
  | Print   of unit
  [@@deriving sexp]

type answer =
  | Ack      of unit
  | Feedback of feedback
  | Result   of coq_object list
  [@@deriving sexp]

