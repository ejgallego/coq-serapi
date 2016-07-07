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

(* Cost analysis: in the past we used to pay almost 3MiB of overload.
 * Now, thanks to smarter linking flags we are paying ~500k for the whole
 * of SerTOP when compared with jsCoq which is IMHO amazing.
 *
 * Unfortunately Core_kernel makes us pay ~1.8MiB of size, so it is too
 * much for now until we figure out a better linking strategy. We manually
 * embed a few utilities functions in the below `Extra` module meanwhile.
 *)

open Sexplib.Conv

module Extra = struct

  let hd_opt l = match l with
    | []     -> None
    | x :: _ -> Some x

  let mem l e = List.mem e l
  let sub s ~pos ~len = String.sub s pos len

  let value     x ~default    = Option.default default x
  let value_map x ~default ~f = Option.cata f default x

  (******************************************************************************)
  (* Taken from Core_kernel, (c) Jane Street, releaser under Apache License 2.0 *)
  let is_prefix_gen =
    let rec loop s ~prefix ~char_equal i =
      i < 0
      || ((char_equal prefix.[i] s.[i])
          && loop s ~prefix ~char_equal (i - 1))
    in
    fun s ~prefix ~char_equal ->
      let prefix_len = String.length prefix in
      String.length s >= prefix_len && loop s ~prefix ~char_equal (prefix_len - 1)

  let is_prefix s ~prefix = is_prefix_gen s ~prefix ~char_equal:(fun x y -> x = y)

  let split_while xs ~f =
    let rec loop acc = function
      | hd :: tl when f hd -> loop (hd :: acc) tl
      | t -> (List.rev acc, t)
    in
    loop [] xs

  (* End of Core_kernel code, (c) Jane Street *)
  (******************************************************************************)

end

(******************************************************************************)
(* SerAPI protocol & interpreter. *)
(******************************************************************************)

exception NoSuchState of Stateid.t

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
  | CoqString   of string
  | CoqSList    of string list
  | CoqRichpp   of Richpp.richpp
  (* XXX: For xml-like printing, should be moved to an option... *)
  (* | CoqRichXml  of Richpp.richpp *)
  | CoqLoc      of Loc.t
  | CoqOption   of Goptions.option_name * Goptions.option_state
  | CoqConstr   of Constr.constr
  | CoqExpr     of Constrexpr.constr_expr
  | CoqTactic   of Names.KerName.t * Tacenv.ltac_entry
  | CoqQualId   of Libnames.qualid
  | CoqGlobRef  of Globnames.global_reference
  | CoqImplicit of Impargs.implicits_list
  | CoqProfData of Profile_ltac.ltacprof_results
  (* Fixme *)
  | CoqGoal     of (Constr.constr * (Names.Id.t list * Constr.constr option * Constr.constr) list) Proof.pre_goals

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

let gen_pp_obj (obj : coq_object) : Pp.std_ppcmds =
  match obj with
  | CoqString  s    -> Pp.str s
  | CoqSList   s    -> Pp.(pr_sequence str) s
  | CoqRichpp  s    -> Pp.str (Richpp.raw_print s)
  (* | CoqRichXml x    -> Serapi_pp.pp_xml fmt (Richpp.repr x) *)
  | CoqLoc    _loc  -> Pp.mt ()
  | CoqOption (n,s) -> pp_opt n s
  | CoqConstr  c    -> Printer.pr_lconstr c
  | CoqExpr    e    -> Ppconstr.pr_lconstr_expr e
  | CoqTactic(kn,_) -> Names.KerName.print kn
  (* Fixme *)
  | CoqGoal    g    -> Pp.pr_sequence pp_goal g.Proof.fg_goals
  | CoqProfData _pf -> Pp.str "FIXME UPSTREAM, provide pr_prof_results"
  | CoqQualId qid   -> Pp.str (Libnames.string_of_qualid qid)
  | CoqGlobRef _gr  -> Pp.str "FIXME GlobRef"
  | CoqImplicit(_,l)-> Pp.pr_sequence pp_implicit l
  (* | CoqPhyLoc(_,_,s)-> pr (Pp.str s) *)
  (* | CoqGoal (_,g,_) -> pr (Ppconstr.pr_lconstr_expr g) *)
  (* | CoqGlob   g -> pr (Printer.pr_glob_constr g) *)

let str_pp_obj fmt (obj : coq_object)  =
  Format.fprintf fmt "%a" (Pp.pp_with ?pp_tag:None) (gen_pp_obj obj)

(** Print output format  *)
type print_format =
  | PpSer
  | PpStr
  | PpRichpp

(* register printer *)

type print_opt = {
  pp_format : print_format  [@default PpStr];
  pp_depth  : int           [@default 0];
  pp_elide  : string        [@default "..."];
  (* pp_margin : int; *)
}

let obj_print pr_opt obj =
  let open Format in
  match pr_opt.pp_format with
  | PpSer    -> obj
  | PpRichpp -> CoqRichpp (Richpp.richpp_of_pp (gen_pp_obj obj))
  | PpStr ->
    let mb      = pp_get_max_boxes     str_formatter () in
    let et      = pp_get_ellipsis_text str_formatter () in
    pp_set_max_boxes     str_formatter pr_opt.pp_depth;
    pp_set_ellipsis_text str_formatter pr_opt.pp_elide;

    fprintf str_formatter "@[%a@]" str_pp_obj obj;
    let str_obj = CoqString (flush_str_formatter ())    in

    pp_set_max_boxes     str_formatter mb;
    pp_set_ellipsis_text str_formatter et;
    str_obj

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
  | e when CErrors.noncritical e ->
    let (e, info) = CErrors.push e in
    Util.iraise (e, info)

(* TODO *)

(******************************************************************************)
(* Answer Types                                                               *)
(******************************************************************************)

(* XXX: Fixme: adapt to 4.03 matching? *)
type answer_kind =
  | Ack
  | StmCurId    of Stateid.t
  | StmAdded    of Stateid.t * Loc.t * [`NewTip | `Unfocus of Stateid.t ]
  | StmCanceled of Stateid.t list
  | StmEdited   of                     [`NewTip | `Focus   of Stm.focus ]
  | ObjList     of coq_object list
  | CoqExn      of exn
  | Completed

(******************************************************************************)
(* Control Sub-Protocol                                                       *)
(******************************************************************************)

(* Simple protection for Coq-generated exceptions *)
let coq_protect e =
  try  e () @ [Completed]
  with exn -> [CoqExn exn]

type add_opts = {
  lim    : int       sexp_option;
  ontop  : Stateid.t sexp_option;
  newtip : Stateid.t sexp_option;
  verb   : bool      [@default false];
}

type control_cmd =
  | StmState                                    (* Get the state *)
  | StmAdd     of       add_opts * string       (* Stm.add       *)
  | StmQuery   of       Stateid.t  * string       (* Stm.query     *)
  | StmCancel  of       Stateid.t list            (* Cancel method *)
  | StmEditAt  of       Stateid.t                 (* Stm.edit_at   *)
  | StmObserve of       Stateid.t                 (* Stm.observe   *)
  | StmJoin                                     (* Stm.join      *)
  | StmStopWorker of    string
  | SetOpt     of bool option * Goptions.option_name * Goptions.option_value
  (*              prefix      * path   * implicit   *)
  | LibAdd     of string list * string * bool
  | Quit

let exec_setopt loc n (v : Goptions.option_value) =
  let open Goptions in
  match v with
  | BoolValue b      -> set_bool_option_value_gen loc n b
  | IntValue  i      -> set_int_option_value_gen  loc n i
  | StringValue s    -> set_string_option_value_gen loc n s
  | StringOptValue s -> set_string_option_value_gen loc n (Option.default "" s)

module ControlUtil = struct

  let edit_id = ref 0

  type doc    = Stateid.t list
  let cur_doc : doc ref = ref [Stateid.of_int 1]

  let pp_doc fmt l =
    let open Serapi_pp in
    Format.fprintf fmt "@[%a@]" (pp_list ~sep:" " pp_stateid) l

  let _dump_doc () =
    Format.eprintf "%a@\n%!" pp_doc !cur_doc

  (* let add_sentence st_id pa = *)
  let add_sentence ?newtip ~ontop verb pa sent =
    (* Workaround coq/coq#204 *)
    let loc         = parse_sentence pa                             in
    let new_st, foc = Stm.add ~ontop ?newtip verb (- !edit_id) sent in
    incr edit_id;
    cur_doc := new_st :: !cur_doc;
    new_st, loc, foc

  let add_sentences opts sent =
    (* Workaround coq/coq#204 *)
    let pa = Pcoq.Gram.parsable (Stream.of_string sent) in
    let pos p l = l.Loc.ep - p         in
    let i   = ref 1                    in
    let buf = ref 0                    in
    let acc = ref []                   in
    let rem = ref (String.length sent) in
    let stt = ref (Extra.value opts.ontop ~default:(Stm.get_current_state ())) in
    let check_lim i = Extra.value_map opts.lim ~default:true ~f:(fun lim -> i <= lim) in
    try
      (* XXX: We check that the ontop state is actually in the
       * document to avoid an Anomaly exception.
       *)
      if not (List.mem !stt !cur_doc) then
        raise (NoSuchState !stt);

      while (0 < !rem) && (check_lim !i) do
        let n_st, loc, foc =
          let sent = Extra.sub sent ~pos:!buf ~len:!rem in
          (* Format.eprintf "[lim:%d|i:%d|buf:%d|rem:%d|stt:%d]@\n%!" lim !i !buf !rem (Stateid.T.to_int !stt); *)
          (* Format.eprintf "Sent: %s @\n%!" sent; *)
          add_sentence ?newtip:opts.newtip ~ontop:!stt opts.verb pa sent
        in
        acc := (StmAdded (n_st, loc, foc)) :: !acc;
        rem := !rem - pos !buf loc;
        buf := !buf + pos !buf loc;
        stt := n_st;
        incr i;
        (* Format.eprintf "[lim:%d|i:%d|buf:%d|rem:%d|stt:%d]@\n%!" lim !i !buf !rem (Stateid.T.to_int !stt); *)
      done;
      List.rev !acc
    with
    | End_of_input  -> List.rev !acc
    | exn           -> List.rev (CoqExn exn :: !acc)

  (* We follow a suggestion by Clément to report sentence invalidation
     in a more modular way: When we issue the cancel command, we will
     look for the cancelled part
  *)
  let cancel_interval st (foc : Stm.focus) =
    let open Serapi_pp in
    let fmt = Format.err_formatter in
    Format.fprintf fmt "Cancel interval: [%a -- %a]" pp_stateid st pp_stateid foc.Stm.stop;
    []
    (* eprintf "%d" foc.stop *)
    (* failwith "SeqAPI FIXME, focus not yet supported" *)

  (* We recover the list of states to cancel plus the first valid
     one. The main invariant is that:
     - The state has to belong to the list.
     - The we cancel states that are newer
  *)
  let invalid_range can_st ~incl:include_st =
    let pred st = if include_st then
        Stateid.newer_than st can_st || Stateid.equal st can_st
      else
        Stateid.newer_than st can_st
    in
    if Extra.mem !cur_doc can_st then
      Extra.split_while !cur_doc ~f:pred
    else [], !cur_doc

  let cancel_sentence can_st =
    (* dump_doc (); *)
    let c_ran, k_ran = invalid_range can_st ~incl:true in
    let prev_st      = Extra.value (Extra.hd_opt k_ran) ~default:Stateid.initial in
    match Stm.edit_at prev_st with
    | `NewTip -> cur_doc := k_ran;
                 [StmCanceled c_ran]
    (* - [tip] is the new document tip.
       - [st]   -- [stop] is dropped.
       - [stop] -- [tip]  has been kept.
       - [start] is where the editing zone starts
       - [add] happen on top of [id].
    *)
    | `Focus foc -> cancel_interval can_st foc

  let edit st =
    (* _dump_doc (); *)
    let foc = Stm.edit_at st in
    (* We update our internal document *)
    let c_ran =
      match foc with
      | `NewTip    ->
        let c_ran, k_ran = invalid_range st ~incl:false in
        cur_doc := k_ran;
        c_ran
      | `Focus foc -> ignore (cancel_interval st foc); []
    in
    (* _dump_doc (); *)
    [StmEdited foc; StmCanceled c_ran]

end

let exec_ctrl ctrl =
  coq_protect @@ fun () -> match ctrl with
  | StmState        -> [StmCurId (Stm.get_current_state ())]

  | StmAdd (opt, s) -> ControlUtil.add_sentences opt s

  | StmCancel st    -> List.concat @@ List.map ControlUtil.cancel_sentence st

  | StmEditAt st    -> ControlUtil.edit st

  | StmQuery(st, s) -> Stm.query ~at:st s; []
  | StmObserve st   -> Stm.observe st; []
  | StmJoin         -> Stm.join (); []
  | StmStopWorker w -> Stm.stop_worker w; []

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

(** Filtering predicates *)
type query_pred =
  | Prefix of string
  (* Filter by type   *)
  (* Filter by module *)

let prefix_pred (prefix : string) (obj : coq_object) : bool =
  match obj with
  | CoqString  s    -> Extra.is_prefix s ~prefix
  | CoqSList   _    -> true     (* XXX *)
  | CoqRichpp  _    -> true
  (* | CoqRichXml _    -> true *)
  | CoqLoc     _    -> true
  | CoqOption (n,_) -> Extra.is_prefix (String.concat "." n) ~prefix
  | CoqConstr _     -> true
  | CoqExpr _       -> true
  | CoqTactic(kn,_) -> Extra.is_prefix (Names.KerName.to_string kn) ~prefix
  (* | CoqPhyLoc _     -> true *)
  | CoqQualId _     -> true
  | CoqGlobRef _    -> true
  | CoqProfData _   -> true
  | CoqImplicit _   -> true
  | CoqGoal _       -> true

let gen_pred (p : query_pred) (obj : coq_object) : bool = match p with
  | Prefix s -> prefix_pred s obj

type query_opt =
  { preds : query_pred sexp_list;
    limit : int sexp_option;
    sid   : Stateid.t [@default Stm.get_current_state()];
    pp    : print_opt [@default { pp_format = PpSexp ; pp_depth = 0; pp_elide = "..." } ];
  }

(** XXX: This should be in sync with the object tag!  *)
type query_cmd =
  | Option   (*  *)
  | Search                         (* Search vernacular, we only support prefix by name *)
  | Goals     of Stateid.t           (* Return goals [TODO: Add filtering/limiting options] *)
  | TypeOf    of string
  | Names     of string            (* XXX Move to prefix *)
  | Tactics   of string            (* XXX Print LTAC signatures (with prefix) *)
  | Locate    of string            (* XXX Print LTAC signatures (with prefix) *)
  | Implicits of string            (* XXX Print LTAC signatures (with prefix) *)
  | ProfileData

module QueryUtil = struct

  let _query_names prefix =
    let acc = ref [] in
    Search.generic_search None (fun gr _env _typ ->
        (* Not happy with this at ALL:

           String of qualid is OK, but shortest_qualid_of_global is an
           unacceptable round-trip. I don't really see other option
           than to maintain a prefix-specific table on the Coq side
           capturing all the possible aliases.

        *)
        let name = Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Names.Id.Set.empty gr) in
        if Extra.is_prefix name ~prefix then acc := name :: !acc
    );
    [CoqSList !acc]

  let query_names_locate prefix =
    let all_gr = Nametab.locate_all @@ Libnames.qualid_of_ident (Names.Id.of_string prefix) in
    List.map (fun x -> CoqGlobRef x) all_gr

  (* From @ppedrot *)
  let query_tactics prefix =
    let open Names           in

    let prefix_long kn = Extra.is_prefix (KerName.to_string kn) ~prefix in
    let prefix_best kn =
      try Extra.is_prefix
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
  | Goals sid      -> Option.cata (fun g -> [CoqGoal g]) [] @@ Serapi_goals.get_goals sid
  | Names   prefix -> QueryUtil.query_names_locate prefix
  | Tactics prefix -> List.map (fun (i,t) -> CoqTactic(i,t)) @@ QueryUtil.query_tactics prefix
  | Locate  id     -> List.map (fun qid -> CoqQualId qid) @@ QueryUtil.locate id
  | Implicits id   -> List.map (fun ii -> CoqImplicit ii ) @@ QueryUtil.implicits id
  | ProfileData    -> [CoqProfData (Profile_ltac.get_profiling_results ())]

  | Search         -> [CoqString "Not Implemented"]
  | TypeOf _       -> [CoqString "Not Implemented"]

let obj_filter preds objs =
  List.(fold_left (fun obj p -> filter (gen_pred p) obj) objs preds)

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
  List.map (obj_print opt.pp) res

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
     "  (Print print_opt coq_object) \n"         ^
     "\nSee sertop_protocol.mli for more details.\n\n")

(******************************************************************************)
(* Top-Level Commands                                                         *)
(******************************************************************************)

type cmd =
  | Control    of control_cmd
  | Print      of print_opt * coq_object
  | Parse      of int * string
  | Query      of query_opt * query_cmd
  | Noop
  | Help

let exec_cmd (cmd : cmd) = match cmd with
  | Control ctrl      -> exec_ctrl ctrl

  | Print(opts, obj)  -> [ObjList [obj_print opts obj]]

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

type cmd_tag    = string
type tagged_cmd = cmd_tag * cmd

type answer =
  | Answer    of cmd_tag * answer_kind
  | Feedback  of Feedback.feedback

