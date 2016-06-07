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

open Ser_goptions
open Ser_stateid
open Ser_feedback
open Ser_constr
open Ser_glob_term

(* New protocol plus interpreter *)

type control_cmd =
  | StmInit                     (* Init Coq      *)
  | StmState                    (* Get the state *)
  | StmAdd     of stateid * string
  | StmEdit    of stateid
  | StmObserve of stateid
  | SetOpt     of unit
  | Quit
  [@@deriving of_sexp]

(* We'd like to use GADT here, but deriving sexp doesn't support them, we will
   need to delay this for now.
*)
(* See https://github.com/c-cube/cconv to see if we could fix that *)
(* type _ query_cmd = *)
(*   | Option : string query_cmd *)
(*   | Search : string query_cmd *)
(*   | Goals  : unit -> int query_cmd *)
(*   [@@deriving sexp] *)

type pp_opt = PpSexp | PpStr
  [@@deriving of_sexp]

(** Max number of results to return, 0 will return a summary *)
type query_limit = int option
  [@@deriving of_sexp]

type query_opt = query_limit * pp_opt
  [@@deriving of_sexp]

type query_cmd =
  | Option of string            (* Search for the value of an option *)
  | Search of string            (* Search vernacular *)
  | Goals                       (* Return goals [TODO: Add filtering/limiting options] *)
  [@@deriving of_sexp]

type coq_object =
  | CoqOption of option_state
  | CoqConstr of constr
  | CoqGlob   of glob_constr
  [@@deriving sexp]

type cmd =
  | Control    of control_cmd
  | Query      of query_opt * query_cmd
  | Print      of coq_object
  [@@deriving of_sexp]

type answer =
  | Ack         of int          (* Command id *)
  | StmInfo     of stateid
  (* | Feedback    of feedback *)
  | QueryResult of coq_object list
  | Printer     of (Format.formatter -> unit)
  [@@deriving sexp_of]

(* type focus = { start : Stateid.t; stop : Stateid.t; tip : Stateid.t } *)
(* val edit_at : Stateid.t -> [ `NewTip | `Focus of focus ] *)
(*     Stateid.t * [ `NewTip | `Unfocus of Stateid.t ] *)

let obj_print (popt : pp_opt) (obj : coq_object) =
  let pr pp obj fmt = Format.fprintf fmt "%a" pp obj in
  match popt, obj with
  | PpStr,  CoqOption _ -> failwith "Fix goptions.mli in Coq to export the proper interface"
  | PpSexp, CoqOption o -> pr Sexp.pp (sexp_of_option_state o)
  | PpStr,  CoqConstr c -> pr (Pp.pp_with ?pp_tag:None) (Printer.pr_constr c)
  | PpSexp, CoqConstr c -> pr Sexp.pp (sexp_of_constr c)
  | PpStr,  CoqGlob   g -> pr (Pp.pp_with ?pp_tag:None) (Printer.pr_glob_constr g)
  | PpSexp, CoqGlob   g -> pr Sexp.pp (sexp_of_glob_constr g)

let fb_handler fb =
  Format.printf "%a@\n%!" Sexp.pp_hum (sexp_of_feedback fb)

let rec read_cmd in_channel =
  let cmd_sexp = Sexplib.Sexp.input_sexp in_channel in
  try cmd_of_sexp cmd_sexp
  with _ ->
    Format.eprintf "Parsing Error@\n%!";
    read_cmd in_channel

let exec_ctrl (ctrl : control_cmd) = match ctrl with
  | StmInit        -> let st = Ser_init.coq_init { Ser_init.fb_handler = fb_handler; } in
                      [StmInfo st]

  | StmState       -> [StmInfo (Stm.get_current_state ())]
  | StmAdd (st, s) ->
    let verb      = true                       in
    let new_st, _ = Stm.add ~ontop:st verb 0 s in
    [StmInfo new_st]
  | StmEdit st     ->
    ignore (Stm.edit_at st);
    [Ack 0]
  | StmObserve st  -> Stm.observe st; [Ack 1]
  | SetOpt _       -> failwith "TODO"
  | Quit           -> [Ack 2]

let exec_cmd (cmd : cmd) = match cmd with
  | Control ctrl      -> exec_ctrl ctrl
  | Query (_opt,_qry) -> [Ack 0; QueryResult []]
  | Print obj         -> [Printer (obj_print PpStr obj)]

  (* Ser_protocol *)
  (* try *)
  (*   let new_state, _ = Stm.add ~ontop:old_state verb 0 (read_line ()) in *)
  (*   (\* Execution *\) *)
  (*   begin try *)
  (*       Stm.finish (); *)
  (*       loop new_state *)
  (*     (\* Execution error *\) *)
  (*     with exn -> *)
  (*       Format.eprintf "%a@\n%!" Sexp.pp_hum (Conv.sexp_of_exn exn); *)
  (*       ignore (Stm.edit_at old_state); *)
  (*       loop old_state *)
  (*   end *)
  (* with *)
  (* (\* End of input *\) *)
  (* | End_of_file -> old_state *)
  (* (\* Parse error *\) *)
  (* | exn -> *)
  (*   Format.eprintf "%a@\n%!" Sexp.pp_hum (Conv.sexp_of_exn exn); *)
  (*   loop old_state *)

  (* let istate = Ser_init.coq_init { Ser_init.fb_handler = fb_handler; } in *)
  (* Format.printf "Coq initialized with state: %s@\n" (Stateid.to_string istate); *)
  (* Format.printf "Coq      exited with state: %s@\n" (Stateid.to_string (loop istate)); *)
  (* () *)
