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
  | StmInit                        (* Init Coq      *)
  | StmState                       (* Get the state *)
  | StmAdd     of stateid * string (* Stm.add       *)
  | StmQuery   of stateid * string (* Stm.query     *)
  | StmEdit    of stateid          (* Stm.edit_at   *)
  | StmObserve of stateid          (* Stm.observe   *)
  | SetOpt     of unit             (* set_option    *)
  | LibAdd     of string list * string * bool
  | Quit
  [@@deriving of_sexp]

(* We'd like to use GADTs here, but deriving sexp doesn't support them *)
(* type _ query_cmd = *)
(*   | Option : string query_cmd *)
(*   | Search : string query_cmd *)
(*   | Goals  : constr query_cmd *)
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
  | CoqString of string
  | CoqOption of option_state
  | CoqConstr of constr
  | CoqGlob   of glob_constr
  [@@deriving sexp]

let exec_query (_limit, _pp) (cmd : query_cmd) = match cmd with
  | Option _ -> failwith "Query option TODO"
  | Search _ -> failwith "Query Search TODO"
  | Goals    -> []

type cmd =
  | Control    of control_cmd
  | Query      of query_opt * query_cmd
  | Print      of coq_object
  [@@deriving of_sexp]

type answer_kind =
  | Ack
  | StmInfo of stateid
  | ObjList of coq_object list
  | CoqExn  of exn
  [@@deriving sexp_of]

(* type focus = { start : Stateid.t; stop : Stateid.t; tip : Stateid.t } *)
(* val edit_at : Stateid.t -> [ `NewTip | `Focus of focus ] *)
(*     Stateid.t * [ `NewTip | `Unfocus of Stateid.t ] *)

type answer =
  | Answer   of int * answer_kind
  | Feedback of feedback
  | SexpError
  [@@deriving sexp_of]

let out_answer fmt a =
  Format.fprintf fmt "@[%a@]@\n%!" Sexp.pp (sexp_of_answer a)

(* XXX: remove the std_formatter ??? *)
let fb_handler fb = out_answer Format.std_formatter (Feedback fb)

let obj_printer fmt (obj : coq_object) =
  let pr obj = Format.fprintf fmt "%a" (Pp.pp_with ?pp_tag:None) obj in
  match obj with
  | CoqString s -> pr (Pp.str s)
  | CoqOption _ -> failwith "Fix goptions.mli in Coq to export the proper interface"
  | CoqConstr c -> pr (Printer.pr_constr c)
  | CoqGlob   g -> pr (Printer.pr_glob_constr g)

let read_cmd in_channel out_fmt =
  let rec read_loop () =
    let cmd_sexp = Sexplib.Sexp.input_sexp in_channel in
    try cmd_of_sexp cmd_sexp
    with _ -> out_answer out_fmt SexpError;
              read_loop ()
  in read_loop ()

(* XXX *)
let verb = true

let coq_protect e =
  try  e
  with exn -> [CoqExn exn]

let exec_ctrl cmd_id (ctrl : control_cmd) = match ctrl with
  | StmInit        -> let st = Ser_init.coq_init { Ser_init.fb_handler = fb_handler; } in
                      [StmInfo st]

  | StmState       -> [StmInfo (Stm.get_current_state ())]
  | StmAdd (st, s) -> coq_protect @@
                      let new_st, _ = Stm.add ~ontop:st verb (-cmd_id) s in
                      [StmInfo new_st]
  | StmQuery(st, s)-> coq_protect (Stm.query ~at:st s; [])
  | StmEdit st     -> coq_protect (ignore (Stm.edit_at st); [])
  | StmObserve st  -> coq_protect (Stm.observe st; [])
  | LibAdd(lib, lib_path, has_ml) ->
    let open Names in
    let coq_path = DirPath.make @@ List.rev @@ List.map Id.of_string lib in
    Loadpath.add_load_path lib_path coq_path ~implicit:false;
    if has_ml then Mltop.add_ml_dir lib_path; []
  | SetOpt _       -> failwith "TODO"
  | Quit           -> []

let exec_cmd cmd_id (cmd : cmd) = match cmd with
  | Control ctrl      -> exec_ctrl cmd_id ctrl
  | Query (opt, qry)  -> [ObjList (exec_query opt qry)]
  | Print obj         ->
    let open Format in
    fprintf str_formatter "@[%a@]" obj_printer obj;
    [ObjList [CoqString (flush_str_formatter ())]]

let ser_loop in_c out_c =
  let open Format in
  let out_fmt    = formatter_of_out_channel out_c            in
  let ack cmd_id = out_answer out_fmt (Answer (cmd_id, Ack)) in
  let rec loop cmd_id =
    let cmd = read_cmd in_c out_fmt                          in
    ack cmd_id;
    List.iter (out_answer out_fmt) @@ List.map (fun a -> Answer (cmd_id, a)) (exec_cmd cmd_id cmd);
    loop (cmd_id + 1)
  in loop 0

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
