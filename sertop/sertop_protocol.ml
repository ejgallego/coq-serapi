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

(* New protocol + interpreter *)

(******************************************************************************)
(* Auxiliary Definitions                                                      *)
(******************************************************************************)

(******************************************************************************)
(* Basic Protocol Objects                                                     *)
(******************************************************************************)

(* We'd like to use GADTs here, but we'd need to pack them somehow to
 * support serialization both ways, see Jérémie's Dimino comment here:
 *
 * https://github.com/janestreet/ppx_sexp_conv/issues/8
 *
 * We need a type of tags + some packing, then:
 *
 * type _ object =
 *   | Option : option      object
 *   | Search : string list object
 *   | Goals  : goals       object
 *   [@@deriving sexp]
 *)

type coq_object =
  | CoqString  of string
  | CoqRichpp  of richpp
  (* XXX: For xml-like printing, should be moved to an option... *)
  | CoqRichXml of richpp
  | CoqOption  of option_name * option_state
  | CoqConstr  of constr
  | CoqExpr    of constr_expr
  (* Fixme *)
  | CoqGoal    of (constr * (id list * constr option * constr) list) pre_goals
  [@@deriving sexp]

(******************************************************************************)
(* Printing Sub-Protocol                                                      *)
(******************************************************************************)

let pp_goal (g, hyps) =
  let open Pp      in
  let open Printer in
  let pr_idl idl = prlist_with_sep (fun () -> str ", ") Names.Id.print idl in
  let pr_lconstr_opt c = str " := " ++ pr_lconstr c in
  let pr_hdef = Option.cata pr_lconstr_opt (mt ())  in
  let pr_hyp (idl, hdef, htyp) =
    pr_idl idl ++ pr_hdef hdef ++ (str " : ") ++ Printer.pr_lconstr htyp in
  pr_vertical_list pr_hyp hyps         ++
  str "============================\n" ++
  Printer.pr_lconstr g

let pp_opt_value (s : option_value) = match s with
  | Goptions.BoolValue b      -> Pp.bool b
  | Goptions.IntValue  i      -> Pp.pr_opt Pp.int i
  | Goptions.StringValue s    -> Pp.str s
  | Goptions.StringOptValue s -> Pp.pr_opt Pp.str s

let pp_opt n s =
  let open Pp in
  str (String.concat "." n) ++ str " := " ++ pp_opt_value s.Goptions.opt_value

let pp_obj fmt (obj : coq_object) =
  let pr obj = Format.fprintf fmt "%a" (Pp.pp_with ?pp_tag:None) obj in
  match obj with
  | CoqString  s    -> pr (Pp.str s)
  | CoqRichpp  s    -> pr (Pp.str (Richpp.raw_print s))
  | CoqRichXml x    -> Sertop_util.pp_xml fmt (Richpp.repr x)
  | CoqOption (n,s) -> pr (pp_opt n s)
  | CoqConstr  c    -> pr (Printer.pr_lconstr c)
  | CoqExpr    e    -> pr (Ppconstr.pr_lconstr_expr e)
  (* Fixme *)
  | CoqGoal    g    -> pr (Pp.pr_sequence pp_goal g.fg_goals)
  (* | CoqGoal (_,g,_) -> pr (Ppconstr.pr_lconstr_expr g) *)
  (* | CoqGlob   g -> pr (Printer.pr_glob_constr g) *)

let string_of_obj obj =
  let open Format in
  fprintf str_formatter "@[%a@]" pp_obj obj;
  CoqString (flush_str_formatter ())

(******************************************************************************)
(* Parsing Sub-Protocol                                                       *)
(******************************************************************************)

(* TODO *)

(******************************************************************************)
(* Answer Types                                                               *)
(******************************************************************************)

(* XXX: Fixme: adapt to 4.03 matching? *)
exception AnswerExn of Sexp.t
let exn_of_sexp sexp = AnswerExn sexp

type answer_kind =
  | Ack
  | StmInfo of stateid * [`NewTip | `Unfocus of stateid | `Focus of focus] option
  | ObjList of coq_object list
  | CoqExn  of exn
  | Completed
  [@@deriving sexp]

(******************************************************************************)
(* Control Sub-Protocol                                                       *)
(******************************************************************************)

(* Simple protection for Coq-generated exceptions *)
let coq_protect e =
  try  e () @ [Completed]
  with exn -> [CoqExn exn]

let verb = true
type control_cmd =
  | StmState                       (* Get the state *)
  | StmAdd     of stateid * string (* Stm.add       *)
  | StmQuery   of stateid * string (* Stm.query     *)
  | StmEditAt  of stateid          (* Stm.edit_at   *)
  | StmObserve of stateid          (* Stm.observe   *)
  | SetOpt     of bool option * option_name * option_value
  (*              prefix      * path   * implicit   *)
  | LibAdd     of string list * string * bool
  | Quit
  [@@deriving sexp]

(******************************************************************************)
(* HACK: Can't this be done automatically *)
let cast_add (r : [`NewTip | `Unfocus of stateid]) : [`NewTip | `Unfocus of stateid | `Focus of focus] =
  match r with
  | `NewTip     -> `NewTip
  | `Unfocus st -> `Unfocus st

let cast_edit (r : [`NewTip | `Focus of focus]) : [`NewTip | `Unfocus of stateid | `Focus of focus] =
  match r with
  | `NewTip   -> `NewTip
  | `Focus fc -> `Focus fc
(* HACK: Can't this be done automatically *)
(******************************************************************************)

let exec_setopt loc n (v : option_value) =
  let open Goptions in
  match v with
  | BoolValue b      -> set_bool_option_value_gen loc n b
  | IntValue  i      -> set_int_option_value_gen  loc n i
  | StringValue s    -> set_string_option_value_gen loc n s
  | StringOptValue s -> set_string_option_value_gen loc n (Option.default "" s)

let exec_ctrl cmd_id (ctrl : control_cmd) =
  coq_protect @@ fun () -> match ctrl with
  | StmState       -> [StmInfo (Stm.get_current_state (), None)]

  | StmAdd (st, s) -> let new_st, foc = Stm.add ~ontop:st verb (-cmd_id) s in
                      [StmInfo (new_st, Some (cast_add foc))]

  | StmEditAt st   -> let foc = Stm.edit_at st in
                      [StmInfo (st, Some (cast_edit foc))]

  | StmQuery(st, s)-> Stm.query ~at:st s; []
  | StmObserve st  -> Stm.observe st; []

  | LibAdd(lib, lib_path, has_ml) ->
                      let open Names in
                      let coq_path = DirPath.make @@ List.rev @@ List.map Names.Id.of_string lib in
                      (* XXX [upstream]: Unify ML and .vo library paths.  *)
                      Loadpath.add_load_path lib_path coq_path ~implicit:false;
                      if has_ml then Mltop.add_ml_dir lib_path;
                      []

  | SetOpt(loc, n, v) -> exec_setopt loc n v; []

  | Quit           -> []

(******************************************************************************)
(* Query Sub-Protocol                                                         *)
(******************************************************************************)

(** Max number of results to return, 0 will return a summary *)
type query_limit = int option
  [@@deriving sexp]

(** Filtering predicates *)
type query_pred =
  | Prefix of string
  (* Filter by type   *)
  (* Filter by module *)
  [@@deriving sexp]

let prefix_pred (prefix : string) (obj : coq_object) : bool =
  let open Core_kernel.Std in
  match obj with
  | CoqString  s    -> String.is_prefix s ~prefix
  | CoqRichpp  _    -> true
  | CoqRichXml _    -> true
  | CoqOption (n,_) -> String.is_prefix (String.concat ~sep:"." n) ~prefix
  | CoqConstr _     -> true
  | CoqExpr _       -> true
  | CoqGoal _       -> true

let f_pred (p : query_pred) (obj : coq_object) : bool = match p with
  | Prefix s -> prefix_pred s obj

(** Query output format  *)
type query_pp =
  | PpSexp
  | PpStr
  [@@deriving sexp]

type query_opt = query_pred list * query_limit * query_pp
  [@@deriving sexp]

(** XXX: This should be in sync with the object tag!  *)
type query_cmd =
  | Option   (*  *)
  | Search   (* Search vernacular, we only support prefix by name *)
  | Goals    (* Return goals [TODO: Add filtering/limiting options] *)
  [@@deriving sexp]

let obj_query (cmd : query_cmd) : coq_object list =
  match cmd with
  | Option -> let table = Goptions.get_tables ()            in
              let opts  = Goptions.OptionMap.bindings table in
              List.map (fun (n,s) -> CoqOption(n,s)) opts
  | Search -> [CoqString "Not Implemented"]
  | Goals  ->
    match Sertop_goals.get_goals () with
    | None   -> []
    | Some g -> [CoqGoal g]

let obj_filter preds objs =
  let open List in
  fold_left (fun obj p -> filter (f_pred p) obj) objs preds

(* XXX: OCaml! .... *)
let rec take n l =
  if n = 0 then [] else match l with
    | []      -> []
    | x :: xs -> x :: take (n-1) xs

let obj_limit limit objs =
  match limit with
  | None   -> objs
  | Some n -> take n objs

let exec_query (pred, limit, pp) cmd =
  let res = obj_query cmd        in
  (* XXX: Filter should move to query once we have GADT *)
  let res = obj_filter pred  res in
  let res = obj_limit  limit res in
  match pp with
    | PpStr  -> List.map string_of_obj res
    | PpSexp -> res

(******************************************************************************)
(* Help                                                                       *)
(******************************************************************************)

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

(******************************************************************************)
(* Top-Level Commands                                                         *)
(******************************************************************************)

type cmd =
  | Control    of control_cmd
  | Print      of coq_object
  | Parse      of string
  | Query      of query_opt * query_cmd
  | Noop
  | Help
  [@@deriving sexp]

type answer =
  | Answer    of int * answer_kind
  | Feedback  of feedback
  | SexpError of Sexp.t
  [@@deriving sexp]

let exec_cmd cmd_id (cmd : cmd) = match cmd with
  | Control ctrl      -> exec_ctrl cmd_id ctrl

  | Print obj         -> [ObjList [string_of_obj obj]]

  | Parse _           -> [ObjList [CoqString "Not yet Implemented"]]

  | Query (opt, qry)  -> [ObjList (exec_query opt qry)]

  | Noop              -> []
  | Help              -> serproto_help (); []

let is_cmd_quit cmd = match cmd with
  | Control Quit -> true
  | _            -> false

(******************************************************************************)
(* Global Protocol Options                                                    *)
(******************************************************************************)

type ser_opts = {
  coqlib   : string option;       (* Whether we should load the prelude, and its location *)
  in_chan  : in_channel;          (* Input/Output channels                                *)
  out_chan : out_channel;
  human    : bool;                (* Output function to use                               *)
  print0   : bool;
  lheader  : bool;
}

(******************************************************************************)
(* Prelude Hacks (to be removed)                                              *)
(******************************************************************************)
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

(******************************************************************************)
(* Input/Output                                                               *)
(******************************************************************************)
(*                                                                            *)
(* Until this point, we've been independent of a particular format or         *)
(* or serialization, with all the operations defined at the symbolic level.   *)
(*                                                                            *)
(* It is now time to unfortunately abandon our fairy-tale and face the real,  *)
(* ugly world in these last 40 lines!                                         *)
(*                                                                            *)
(******************************************************************************)

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

let out_answer opts =
  let open Format                                                               in
  let pp_sexp = if opts.human  then Sexp.pp_hum                   else Sexp.pp  in
  let pp_term = if opts.print0 then fun fmt () -> fprintf fmt "%c" (Char.chr 0)
                               else fun fmt () -> fprintf fmt "@\n"             in
  if opts.lheader then
    fun fmt a ->
      fprintf str_formatter "@[%a@]%a%!" pp_sexp (sexp_of_answer a) pp_term ();
      let out = flush_str_formatter () in
      fprintf fmt "@[byte-length: %d@\n%s@]%!" (String.length out) out
  else
    fun fmt a -> fprintf fmt "@[%a@]%a%!" pp_sexp (sexp_of_answer a) pp_term ()

let ser_loop ser_opts =
  let open List   in
  let open Format in
  let out_fmt      = formatter_of_out_channel ser_opts.out_chan        in
  let pp_answer an = out_answer ser_opts out_fmt an                    in
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
    (* XXX: This protection should be unnecesary when we complete our
       toplevel *)
    iter pp_answer @@ map (fun a  -> Answer (cmd_id, a)) (exec_cmd cmd_id cmd);
    if not (is_cmd_quit cmd) then loop (cmd_id + 1)
  in loop 0
