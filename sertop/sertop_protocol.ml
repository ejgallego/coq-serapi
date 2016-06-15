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
open Sexplib.Conv

open Ser_loc
open Ser_names
open Ser_goptions
open Ser_stateid
open Ser_richpp
open Ser_feedback
open Ser_libnames
open Ser_impargs
(* open Ser_library *)
open Ser_constr
open Ser_constrexpr
open Ser_proof
open Ser_stm
open Ser_tacenv

(* New protocol + interpreter *)

(******************************************************************************)
(* Exception Registration                                                     *)
(******************************************************************************)

(* We play slow for now *)
let _ =
  (* XXX Finish this *)
  let open Sexp in
  let sexp_of_std_ppcmds pp = Atom (Pp.string_of_ppcmds pp) in
  Conv.Exn_converter.add_slow (function
      | Errors.UserError(e,msg) -> 
        Some (List [Atom "Errors.UserError"; List [Atom e; sexp_of_std_ppcmds msg]])
      | Errors.AlreadyDeclared msg ->
        Some (List [Atom "Errors.AlreadyDeclared"; List [sexp_of_std_ppcmds msg]])
(* Sadly private... request Coq devs to make them public?
      | Cerrors.EvaluatedError(msg, exn) -> Some (
          match exn with
          | Some exn -> List [Atom "CError.EvaluatedError"; sexp_of_std_ppcmds msg; sexp_of_exn exn]
          | None     -> List [Atom "CError.EvaluatedError"; sexp_of_std_ppcmds msg]
        )
      | Errors.Anomaly(msgo, pp) ->
        Some (List [Atom "Anomaly"; sexp_of_option sexp_of_string msgo; sexp_of_std_ppcmds pp])
*)
      | _ -> None

    )


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
  | CoqSList   of string list
  | CoqRichpp  of richpp
  (* XXX: For xml-like printing, should be moved to an option... *)
  | CoqRichXml of richpp
  | CoqLoc     of loc
  | CoqOption  of option_name * option_state
  | CoqConstr  of constr
  | CoqExpr    of constr_expr
  | CoqTactic  of kername * ltac_entry
  | CoqQualId  of qualid
  | CoqImplicit of implicits_list
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

let pp_opt_value (s : Goptions.option_value) = match s with
  | Goptions.BoolValue b      -> Pp.bool b
  | Goptions.IntValue  i      -> Pp.pr_opt Pp.int i
  | Goptions.StringValue s    -> Pp.str s
  | Goptions.StringOptValue s -> Pp.pr_opt Pp.str s

let pp_opt n s =
  let open Pp in
  str (String.concat "." n) ++ str " := " ++ pp_opt_value s.Goptions.opt_value

let pp_implicit = function
  | None               -> Pp.str "!"
  | Some (iname, _, _) -> Names.Id.print iname

let pp_obj fmt (obj : coq_object) =
  let pr obj = Format.fprintf fmt "%a" (Pp.pp_with ?pp_tag:None) obj in
  match obj with
  | CoqString  s    -> pr (Pp.str s)
  | CoqSList   s    -> pr (Pp.(pr_sequence str) s)
  | CoqRichpp  s    -> pr (Pp.str (Richpp.raw_print s))
  | CoqRichXml x    -> Sertop_pp.pp_xml fmt (Richpp.repr x)
  | CoqLoc    _loc  -> pr (Pp.mt ())
  | CoqOption (n,s) -> pr (pp_opt n s)
  | CoqConstr  c    -> pr (Printer.pr_lconstr c)
  | CoqExpr    e    -> pr (Ppconstr.pr_lconstr_expr e)
  | CoqTactic(kn,_) -> pr (Names.KerName.print kn)
  (* Fixme *)
  | CoqGoal    g    -> pr (Pp.pr_sequence pp_goal g.fg_goals)
  | CoqQualId qid   -> pr (Pp.str (Libnames.string_of_qualid qid))
  | CoqImplicit(_,l)-> pr (Pp.pr_sequence pp_implicit l)
  (* | CoqPhyLoc(_,_,s)-> pr (Pp.str s) *)
  (* | CoqGoal (_,g,_) -> pr (Ppconstr.pr_lconstr_expr g) *)
  (* | CoqGlob   g -> pr (Printer.pr_glob_constr g) *)

let string_of_obj obj =
  let open Format in
  fprintf str_formatter "@[%a@]" pp_obj obj;
  CoqString (flush_str_formatter ())

(******************************************************************************)
(* Parsing Sub-Protocol                                                       *)
(******************************************************************************)

(* Sadly this is not properly exported from Stm/Vernac *)
exception End_of_input

let parse_sentence = Flags.with_option Flags.we_are_parsing
  (fun pa ->
    match Pcoq.Gram.entry_parse Pcoq.main_entry pa with
    | Some (loc, _ast) -> loc
    | None             -> raise End_of_input
  )

(* Accumulate at most num succesful parsing attemps in acc *)
let parse_sentences num acc s =
  let pa = Pcoq.Gram.parsable (Stream.of_string s) in
  (* Not strictly needed *)
  try
    for _i = 1 to num do
      let loc = parse_sentence pa in
      acc := CoqLoc loc :: !acc
    done;
  with
  | End_of_input -> ()
  | e when Errors.noncritical e ->
    let (e, info) = Errors.push e in
    Util.iraise (e, info)

(* TODO *)

(******************************************************************************)
(* Answer Types                                                               *)
(******************************************************************************)

(* XXX: Fixme: adapt to 4.03 matching? *)
exception AnswerExn of Sexp.t
let exn_of_sexp sexp = AnswerExn sexp

type answer_kind =
  | Ack
  | StmCurId    of stateid
  | StmAdded    of stateid * loc * [`NewTip | `Unfocus of stateid ]
  | StmCanceled of stateid list
  | StmEdited of                   [`NewTip | `Focus   of focus   ]
  | ObjList     of coq_object list
  | CoqExn      of exn
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
  | StmState                                    (* Get the state *)
  | StmAdd     of int * stateid option * string (* Stm.add       *)
  | StmQuery   of       stateid        * string (* Stm.query     *)
  | StmCancel  of       stateid list            (* Cancel method *)
  | StmEditAt  of       stateid                 (* Stm.edit_at   *)
  | StmObserve of       stateid                 (* Stm.observe   *)
  | SetOpt     of bool option * option_name * option_value
  (*              prefix      * path   * implicit   *)
  | LibAdd     of string list * string * bool
  | Quit
  [@@deriving sexp]

let exec_setopt loc n (v : option_value) =
  let open Goptions in
  match v with
  | BoolValue b      -> set_bool_option_value_gen loc n b
  | IntValue  i      -> set_int_option_value_gen  loc n i
  | StringValue s    -> set_string_option_value_gen loc n s
  | StringOptValue s -> set_string_option_value_gen loc n (Option.default "" s)

module ControlUtil = struct

  open Core_kernel.Std

  let edit_id = ref 0

  type doc    = stateid list
  let cur_doc : doc ref = ref []

  let pp_doc fmt l =
    let open Sertop_pp in
    Format.fprintf fmt "@[%a@]" (pp_list ~sep:" " pp_stateid) l

  let _dump_doc () =
    Format.eprintf "%a@\n%!" pp_doc !cur_doc

  (* let add_sentence st_id pa = *)
  let add_sentence st_id sent pa =
    (* Workaround coq/coq#204 *)
    let loc         = parse_sentence pa                           in
    let new_st, foc = Stm.add ~ontop:st_id verb (- !edit_id) sent in
    incr edit_id;
    cur_doc := new_st :: !cur_doc;
    new_st, loc, foc

  let add_sentences lim st_id sent =
    (* Workaround coq/coq#204 *)
    let pa = Pcoq.Gram.parsable (Stream.of_string sent) in
    let pos p l =
      let (_,_,_,_,e) = Loc.represent l in (e-p)
    in
    let i   = ref 1                    in
    let acc = ref []                   in
    let buf = ref 0                    in
    let rem = ref (String.length sent) in
    let stt = ref st_id                in
    try
      while (0 < !rem) && (!i <= lim) do
      let n_st, loc, foc =
        let sent = String.sub sent ~pos:!buf ~len:!rem in
        (* Format.eprintf "[lim:%d|i:%d|buf:%d|rem:%d|stt:%d]@\n%!" lim !i !buf !rem (Stateid.to_int !stt); *)
        (* Format.eprintf "Sent: %s @\n%!" sent; *)
        add_sentence !stt sent pa
      in
      acc := (StmAdded (n_st, loc, foc)) :: !acc;
      rem := !rem - pos !buf loc;
      buf := !buf + pos !buf loc;
      stt := n_st;
      incr i;
      (* Format.eprintf "[lim:%d|i:%d|buf:%d|rem:%d|stt:%d]@\n%!" lim !i !buf !rem (Stateid.to_int !stt); *)
      done;
      List.rev !acc
    with End_of_input -> List.rev !acc

  (* We follow a suggestion by Clément to report sentence invalidation
     in a more modular way: When we issue the cancel command, we will
     look for the cancelled part
  *)
  let cancel_interval (_foc : Stm.focus) =
    failwith "SeqAPI FIXME, focus not yet supported"

  (* We recover the list of states to cancel plus the first valid
     one. The main invariant is that:
     - The state has to belong to the list.
     - The we cancel states that are newer
  *)
  let invalid_range_st can_st =
    if List.mem !cur_doc can_st then
      List.split_while !cur_doc
        ~f:(fun st -> Stateid.newer_than st can_st || Stateid.equal st can_st)
    else [], !cur_doc

  let cancel_sentence can_st =
    (* dump_doc (); *)
    let c_ran, k_ran = invalid_range_st can_st in
    let prev_st      = Option.value (List.hd k_ran) ~default:Stateid.initial in
    match Stm.edit_at prev_st with
    | `NewTip -> cur_doc := k_ran;
                 [StmCanceled c_ran]
    (* - [tip] is the new document tip.
       - [st]   -- [stop] is dropped.
       - [stop] -- [tip]  has been kept.
       - [start] is where the editing zone starts
       - [add] happen on top of [id].
    *)
    | `Focus foc -> cancel_interval foc

  let edit st =
    _dump_doc ();
    let foc = Stm.edit_at st in
    (* We update our internal document *)
    begin match foc with
    | `NewTip    -> (if List.mem !cur_doc st then
                       cur_doc := List.drop_while !cur_doc ~f:(fun st_act -> Stateid.newer_than st_act st)
                    )
    | `Focus foc -> ignore (cancel_interval foc)
    end;
    _dump_doc ();
    [StmEdited foc]

end

let exec_ctrl ctrl =
  coq_protect @@ fun () -> match ctrl with
  | StmState       -> [StmCurId (Stm.get_current_state ())]

  | StmAdd (lim, ost, s) -> let st = Option.default (Stm.get_current_state ()) ost in
                            ControlUtil.add_sentences lim st s

  | StmCancel st         -> List.concat @@ List.map ControlUtil.cancel_sentence st

  | StmEditAt st         -> ControlUtil.edit st

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
(* type query_limit = int option *)
(*   [@@deriving sexp] *)

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
  | CoqSList   _    -> true     (* XXX *)
  | CoqRichpp  _    -> true
  | CoqRichXml _    -> true
  | CoqLoc     _    -> true
  | CoqOption (n,_) -> String.is_prefix (String.concat ~sep:"." n) ~prefix
  | CoqConstr _     -> true
  | CoqExpr _       -> true
  | CoqTactic(kn,_) -> String.is_prefix (Names.KerName.to_string kn) ~prefix
  (* | CoqPhyLoc _     -> true *)
  | CoqQualId _     -> true
  | CoqImplicit _   -> true
  | CoqGoal _       -> true

let gen_pred (p : query_pred) (obj : coq_object) : bool = match p with
  | Prefix s -> prefix_pred s obj

(** Query output format  *)
type query_pp =
  | PpSexp
  | PpStr
  [@@deriving sexp]

type query_opt =
  { preds : query_pred sexp_list;
    limit : int sexp_option;
    pp    : query_pp [@default PpSexp];
  } [@@deriving sexp]

(** XXX: This should be in sync with the object tag!  *)
type query_cmd =
  | Option   (*  *)
  | Search   (* Search vernacular, we only support prefix by name *)
  | Goals    (* Return goals [TODO: Add filtering/limiting options] *)
  | TypeOf  of string
  | Names   of string              (* XXX Move to prefix *)
  | Tactics of string              (* XXX Print LTAC signatures (with prefix) *)
  | Locate  of string              (* XXX Print LTAC signatures (with prefix) *)
  | Implicits of string              (* XXX Print LTAC signatures (with prefix) *)
  [@@deriving sexp]

module QueryUtil = struct

  let query_names prefix =
    let acc = ref [] in
    Search.generic_search None (fun gr _env _typ ->
        (* Not happy with this at ALL:

           String of qualid is OK, but shortest_qualid_of_global is an
           unacceptable round-trip. I don't really see other option
           than to maintain a prefix-specific table on the Coq side
           capturing all the possible aliases.

        *)
        let name = Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Names.Id.Set.empty gr) in
        if Core_kernel.Std.String.is_prefix name ~prefix then acc := name :: !acc
    );
    [CoqSList !acc]

  (* From @ppedrot *)
  let query_tactics prefix =
    let open Names           in

    let prefix_long kn = Core_kernel.Std.String.is_prefix (KerName.to_string kn) ~prefix in
    let prefix_best kn =
      try Core_kernel.Std.String.is_prefix
            (Libnames.string_of_qualid (Nametab.shortest_qualid_of_tactic kn)) ~prefix
      with Not_found ->
        (* Debug code, It is weird that shortest_qualid_of_tactic returns a Not_found... :S *)
        (* Format.eprintf "%s has no short name@\n%!" (KerName.to_string kn); *)
        false
    in
    let tpred kn _ = prefix_long kn || prefix_best kn in
    KNmap.bindings @@ KNmap.filter tpred @@ Tacenv.ltac_entries ()
  [@@warning "-44"]

    (* let map (kn, entry) = *)
    (*   let qid = *)
    (*     try Some (Nametab.shortest_qualid_of_tactic kn) *)
    (*     with Not_found -> None *)
    (*   in *)
    (*   match qid with *)
    (*   | None -> None *)
    (*   | Some qid -> Some (qid, entry.Tacenv.tac_body) *)
    (* in *)
    (* List.map  map entries [] *)

  let locate id =
    let open Names     in
    let open Libnames  in
    let open Globnames in
    (* From prettyp.ml *)
    let qid = qualid_of_ident @@ Id.of_string id in
    let expand = function
      | TrueGlobal ref ->
        Nametab.shortest_qualid_of_global Id.Set.empty ref
      | SynDef kn ->
        Nametab.shortest_qualid_of_syndef Id.Set.empty kn
    in
    List.map expand (Nametab.locate_extended_all qid)

  let implicits id =
    let open Names     in
    let open Libnames  in
    try let ref = Nametab.locate (qualid_of_ident (Id.of_string id)) in
      Impargs.implicits_of_global ref
    with Not_found -> []

end

let obj_query (cmd : query_cmd) : coq_object list =
  match cmd with
  | Option         -> let table = Goptions.get_tables ()            in
                      let opts  = Goptions.OptionMap.bindings table in
                      List.map (fun (n,s) -> CoqOption(n,s)) opts
  | Goals          -> Option.cata (fun g -> [CoqGoal g]) [] @@ Sertop_goals.get_goals ()
  | Names   prefix -> QueryUtil.query_names   prefix
  | Tactics prefix -> List.map (fun (i,t) -> CoqTactic(i,t)) @@ QueryUtil.query_tactics prefix
  | Locate  id     -> List.map (fun qid -> CoqQualId qid) @@ QueryUtil.locate id
  | Implicits id   -> List.map (fun ii -> CoqImplicit ii ) @@ QueryUtil.implicits id

  | Search         -> [CoqString "Not Implemented"]
  | TypeOf _       -> [CoqString "Not Implemented"]

let obj_filter preds objs =
  let open List in
  fold_left (fun obj p -> filter (gen_pred p) obj) objs preds

(* XXX: OCaml! .... *)
let rec take n l =
  if n = 0 then [] else match l with
    | []      -> []
    | x :: xs -> x :: take (n-1) xs

let obj_limit limit objs =
  match limit with
  | None   -> objs
  | Some n -> take n objs

let exec_query opt cmd =
  let res = obj_query cmd        in
  (* XXX: Filter should move to query once we have GADT *)
  let res = obj_filter opt.preds res in
  let res = obj_limit  opt.limit res in
  match opt.pp with
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
  | Parse      of int * string
  | Query      of query_opt * query_cmd
  | Noop
  | Help
  [@@deriving sexp]

type cmd_tag = string
  [@@deriving sexp]

type tagged_cmd = cmd_tag * cmd
  [@@deriving sexp]

type answer =
  | Answer    of cmd_tag * answer_kind
  | Feedback  of feedback
  | SexpError of Sexp.t
  [@@deriving sexp]

let exec_cmd (cmd : cmd) = match cmd with
  | Control ctrl      -> exec_ctrl ctrl

  | Print obj         -> [ObjList [string_of_obj obj]]

  (* We try to do a bit better here than a coq_protect would do, by
     trying to keep partial results. *)
  | Parse (num, str)  ->
    let acc = ref [] in
    begin try parse_sentences num acc str; [ObjList (List.rev !acc)]
          with exn -> [ObjList (List.rev !acc)] @ [CoqExn exn]
    end
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
  async    : bool;
}

(******************************************************************************)
(* Prelude Hacks (to be removed)                                              *)
(******************************************************************************)
(* XXX: Stid are fixed here. Move to ser_init? *)
let ser_prelude coq_path : cmd list =
  let mk_path prefix l = coq_path ^ "/" ^ prefix ^ "/" ^ String.concat "/" l in
  List.map (fun p -> Control (LibAdd ("Coq" :: p, mk_path "plugins"  p, true))) Sertop_init.coq_init_plugins  @
  List.map (fun p -> Control (LibAdd ("Coq" :: p, mk_path "theories" p, true))) Sertop_init.coq_init_theories @
  [ Control (StmAdd     (1, None, "Require Import Coq.Init.Prelude. "));
    Control (StmObserve (Stateid.of_int 2))
  ]

let do_prelude coq_path =
  List.iter (fun cmd -> ignore (exec_cmd cmd)) (ser_prelude coq_path)

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

(* XXX: Improve by using manual tag parsing. *)
let read_cmd cmd_id in_channel pp_answer =
  let rec read_loop () =
    try
      let cmd_sexp = Sexp.input_sexp in_channel in
      begin
        try tagged_cmd_of_sexp cmd_sexp
        with
        | End_of_file   -> "EOF", Control Quit
        | _exn ->
          (string_of_int cmd_id), cmd_of_sexp cmd_sexp
      end
    with
    | End_of_file   -> "EOF", Control Quit
    | exn           -> pp_answer (SexpError(sexp_of_exn exn));
                       read_loop ()
  in read_loop ()

(** We could use Sexp.to_string too  *)
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
  Sertop_init.coq_init {
    Sertop_init.fb_handler   = pp_feed;
    Sertop_init.enable_async = ser_opts.async;
  };
  (* Load prelude if requested *)
  Option.iter do_prelude ser_opts.coqlib;

  (* Follow the same approach than coqtop for now: allow Coq to be
   * interrupted by Ctrl-C. Not entirely safe or race free... but we
   * trust the IDEs to send the signal on coherent IO state.
   *)
  Sys.catch_break true;

  (* Main loop *)
  let rec loop cmd_id =
    try
      let cmd_tag, cmd = read_cmd cmd_id ser_opts.in_chan pp_answer in
      pp_ack cmd_tag;
      iter pp_answer @@ map (fun a  -> Answer (cmd_tag, a)) (exec_cmd cmd);
      if not (is_cmd_quit cmd) then loop (1+cmd_id)
    with Sys.Break -> loop (1+cmd_id)
  in loop 0
