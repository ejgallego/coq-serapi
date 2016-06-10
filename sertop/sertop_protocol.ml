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

open Ser_names
open Ser_goptions
open Ser_stateid
open Ser_richpp
open Ser_feedback
open Ser_constr
open Ser_constrexpr
open Ser_proof
open Ser_stm

(* New protocol plus interpreter *)

type control_cmd =
  | StmState                       (* Get the state *)
  | StmAdd     of stateid * string (* Stm.add       *)
  | StmQuery   of stateid * string (* Stm.query     *)
  | StmEditAt  of stateid          (* Stm.edit_at   *)
  | StmObserve of stateid          (* Stm.observe   *)
  | SetOpt     of unit             (* set_option    *)
  (*              prefix      * path   * implicit   *)
  | LibAdd     of string list * string * bool
  | Quit
  [@@deriving sexp]

(* We'd like to use GADTs here, but we'd need to pack them somehow to
 * support serialization both ways, see Jérémie's Dimino comment here:
 *
 * https://github.com/janestreet/ppx_sexp_conv/issues/8
 *
 * type _ query_cmd =
 *   | Option : string query_cmd
 *   | Search : string query_cmd
 *   | Goals  : constr query_cmd
 *   [@@deriving sexp]
 *)

type pp_opt =
  | PpSexp
  | PpStr
  [@@deriving sexp]

(** Max number of results to return, 0 will return a summary *)
type query_limit = int option
  [@@deriving sexp]

type query_opt = query_limit * pp_opt
  [@@deriving sexp]

type query_cmd =
  | Option of string            (* Search for the value of an option *)
  | Search of string            (* Search vernacular *)
  | Goals                       (* Return goals [TODO: Add filtering/limiting options] *)
  [@@deriving sexp]

type coq_object =
  | CoqString  of string
  | CoqRichpp  of richpp
  (* XXX: For xml-like printing, should be moved to an option... *)
  | CoqRichXml of richpp
  | CoqOption  of option_state
  | CoqConstr  of constr
  | CoqExpr    of constr_expr
  (* Fixme *)
  | CoqGoal    of (constr * (id list * constr option * constr) list) pre_goals
  [@@deriving sexp]

let pp_goal (g, hyps) =
  let open Pp      in
  let open Printer in
  let pr_idl idl = prlist_with_sep (fun () -> str ", ") Names.Id.print idl in
  let pr_lconstr_opt c = str " := " ++ pr_lconstr c in
  let pr_hdef = Option.cata pr_lconstr_opt (mt ()) in
  let pr_hyp (idl, hdef, htyp) =
    pr_idl idl ++ pr_hdef hdef ++ (str " : ") ++ Printer.pr_lconstr htyp in
  pr_vertical_list pr_hyp hyps         ++
  str "============================\n" ++
  Printer.pr_lconstr g

let obj_printer fmt (obj : coq_object) =
  let pr obj = Format.fprintf fmt "%a" (Pp.pp_with ?pp_tag:None) obj in
  match obj with
  | CoqString  s -> pr (Pp.str s)
  | CoqRichpp  s -> pr (Pp.str (Richpp.raw_print s))
  | CoqRichXml x -> Sertop_util.pp_xml fmt (Richpp.repr x)
  | CoqOption  _ -> failwith "Fix goptions.mli in Coq to export the proper interface"
  | CoqConstr  c -> pr (Printer.pr_lconstr c)
  | CoqExpr    e -> pr (Ppconstr.pr_lconstr_expr e)
  (* Fixme *)
  | CoqGoal    g -> pr (Pp.pr_sequence pp_goal g.fg_goals)
  (* | CoqGoal (_,g,_) -> pr (Ppconstr.pr_lconstr_expr g) *)
  (* | CoqGlob   g -> pr (Printer.pr_glob_constr g) *)

(* XXX: Fixme: by matching? *)
exception AnswerExn of Sexp.t
let exn_of_sexp sexp = AnswerExn sexp

type answer_kind =
  | Ack
  | StmInfo of stateid * [`NewTip | `Unfocus of stateid | `Focus of focus] option
  | ObjList of coq_object list
  | CoqExn  of exn
  [@@deriving sexp]

(* XXX: Can't this be done automatically *)
let cast_add (r : [`NewTip | `Unfocus of stateid]) : [`NewTip | `Unfocus of stateid | `Focus of focus] =
  match r with
  | `NewTip     -> `NewTip
  | `Unfocus st -> `Unfocus st

let cast_edit (r : [`NewTip | `Focus of focus]) : [`NewTip | `Unfocus of stateid | `Focus of focus] =
  match r with
  | `NewTip   -> `NewTip
  | `Focus fc -> `Focus fc

let obj_print obj =
  let open Format in
  fprintf str_formatter "@[%a@]" obj_printer obj;
  CoqString (flush_str_formatter ())

let exec_raw_query (cmd : query_cmd) : coq_object list =
  match cmd with
  | Option _ -> failwith "Query option TODO"
  | Search _ -> failwith "Query Search TODO"
  | Goals    -> 
    match Sertop_goals.get_goals () with
    | None   -> []
    | Some g -> [CoqGoal g]

let exec_query (_limit, pp) cmd =
  let res = exec_raw_query cmd in
  match pp with
    | PpStr  -> List.map obj_print res
    | PpSexp -> res

type cmd =
  | Control    of control_cmd
  | Query      of query_opt * query_cmd
  | Print      of coq_object
  | Parse      of string
  | Help
  [@@deriving sexp]

(* Prints help to stderr. TODO, we should use a ppx to automatically
   generate the description of the protocol. *)
let serproto_help () =
  let open Format in
  eprintf "%s%!"
    ("Coq SerAPI -- Protocol documentation is still incomplete, main commands are: \n\n" ^
     "  (Control control_cmd) \n"      ^
     "  (Query query_opt query_cmd) \n"^
     "  (Print coq_object) \n"         ^
     "\nSee sertop_protocol.mli for more details.\n\n")

let cmd_quit cmd = match cmd with
  | Control Quit -> true
  | _            -> false

type answer =
  | Answer    of int * answer_kind
  | Feedback  of feedback
  | SexpError of Sexp.t
  [@@deriving sexp]

let out_answer print0 sexp_pp fmt a =
  let open Format in
  let pp_term fmt () = if print0 then fprintf fmt "%c" (Char.chr 0) else fprintf fmt "@\n" in
  fprintf fmt "@[%a@]%a%!" sexp_pp (sexp_of_answer a) pp_term ()

let read_cmd in_channel pp_answer =
  let rec read_loop () =
    try
      let cmd_sexp = Sexp.input_sexp in_channel in
      cmd_of_sexp cmd_sexp
    with
    | End_of_file   -> Control Quit
    | exn           -> pp_answer (SexpError(sexp_of_exn exn));
                       read_loop ()
  in read_loop ()

(* XXX *)
let verb = true

let coq_protect e =
  try  e ()
  with exn -> [CoqExn exn]

let exec_ctrl cmd_id (ctrl : control_cmd) = match ctrl with
  | StmState       -> [StmInfo (Stm.get_current_state (), None)]
  | StmAdd (st, s) -> coq_protect @@ fun () ->
                      let new_st, foc = Stm.add ~ontop:st verb (-cmd_id) s in
                      [StmInfo (new_st, Some (cast_add foc))]
  | StmQuery(st, s)-> coq_protect (fun () -> Stm.query ~at:st s; [])
  | StmEditAt st   -> coq_protect @@ fun () ->
                      let foc = Stm.edit_at st in
                      [StmInfo (st, Some (cast_edit foc))]
  | StmObserve st  -> coq_protect (fun () -> Stm.observe st; [])

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
  | Print obj         -> let open Format in
                         fprintf str_formatter "@[%a@]" obj_printer obj;
                         [ObjList [CoqString (flush_str_formatter ())]]
  | Parse _           -> failwith "TODO: Parsing terms"
  | Help              -> serproto_help (); []

(* XXX: Stid are fixed here. Move to ser_init? *)
let ser_prelude coq_path : cmd list =
  let mk_path prefix l = coq_path ^ "/" ^ prefix ^ "/" ^ String.concat "/" l in
  List.map (fun p -> Control (LibAdd ("Coq" :: p, mk_path "plugins"  p, true))) Sertop_init.coq_init_plugins  @
  List.map (fun p -> Control (LibAdd ("Coq" :: p, mk_path "theories" p, true))) Sertop_init.coq_init_theories @
  [ Control (StmAdd     (Stateid.of_int 1, "Require Import Coq.Init.Prelude. "));
    Control (StmObserve (Stateid.of_int 2))
  ]

let do_prelude coq_path =
  List.iter (fun cmd -> ignore (exec_cmd 0 cmd)) (ser_prelude coq_path)

type ser_opts = {
  coqlib   : string option;       (* Whether we should load the prelude, and its location *)
  in_chan  : in_channel;          (* Input/Output channels                                *)
  out_chan : out_channel;
  human    : bool;                (* Output function to use                               *)
  print0   : bool;
}

let ser_loop ser_opts =
  let open Format in
  let out_fmt      = formatter_of_out_channel ser_opts.out_chan        in
  let pp_sexp      = if ser_opts.human then Sexp.pp_hum else Sexp.pp   in
  let pp_answer an = out_answer ser_opts.print0 pp_sexp out_fmt an     in
  let pp_ack cid   = pp_answer (Answer (cid, Ack))                     in
  let pp_feed fb   = pp_answer (Feedback fb)                           in
  (* Init Coq *)
  Sertop_init.coq_init { Sertop_init.fb_handler = pp_feed; };
  (* Load prelude if requested *)
  Option.iter do_prelude ser_opts.coqlib;
  (* Main loop *)
  let rec loop cmd_id =
    let cmd = read_cmd ser_opts.in_chan pp_answer in
    pp_ack cmd_id;
    List.iter pp_answer @@ List.map (fun a -> Answer (cmd_id, a)) (exec_cmd cmd_id cmd);
    if not (cmd_quit cmd) then loop (cmd_id + 1)
  in loop 0

