(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* Cost analysis: in the past we used to pay almost 3MiB of overload
 * in SerAPI.
 *
 * Now, thanks to smarter linking flags we are paying ~500k for the whole
 * of SerTOP when compared to jsCoq, it is IMHO great.
 *
 * Unfortunately, Core_kernel would cost us ~1.8MiB more, it is too
 * much for now until we figure out a better linking strategy. We manually
 * embed a few utility functions in the `Extra` module below.
 *)

open Ltac_plugin
open Sexplib.Conv

module Extra = struct

  let hd_opt l = match l with
    | []     -> None
    | x :: _ -> Some x

  let mem l e = List.mem e l
  (* let sub s ~pos ~len = String.sub s pos len *)

  let value     x ~default    = Option.default default x
  let value_map x ~default ~f = Option.cata f default x

  (******************************************************************************)
  (* Taken from Core_kernel, (c) Jane Street, released under Apache License 2.0 *)
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

(* XXX: Use a module here to have Coq.String etc...? *)
type coq_object =
  | CoqString    of string
  | CoqSList     of string list
  | CoqPp        of Pp.t
  (* | CoqRichpp    of Richpp.richpp *)
  | CoqLoc       of Loc.t
  | CoqAst       of Vernacexpr.vernac_expr Loc.located
  | CoqOption    of Goptions.option_name * Goptions.option_state
  | CoqConstr    of Constr.constr
  | CoqExpr      of Constrexpr.constr_expr
  | CoqMInd      of Names.MutInd.t * Declarations.mutual_inductive_body
  | CoqTactic    of Names.KerName.t * Tacenv.ltac_entry
  | CoqQualId    of Libnames.qualid
  | CoqGlobRef   of Globnames.global_reference
  | CoqImplicit  of Impargs.implicits_list
  | CoqProfData  of Profile_ltac.treenode
  | CoqNotation  of Constrexpr.notation
  | CoqUnparsing of Notation.unparsing_rule * Notation.extra_unparsing_rules * Notation_term.notation_grammar
  | CoqGoal      of Constr.t               Serapi_goals.reified_goal Proof.pre_goals
  | CoqExtGoal   of Constrexpr.constr_expr Serapi_goals.reified_goal Proof.pre_goals
  | CoqProof     of Goal.goal list
                    * (Goal.goal list * Goal.goal list) list
                    * Goal.goal list
                    * Goal.goal list
                    (* We don't seralize the evar map for now... *)
                    (* * Evd.evar_map *)

(******************************************************************************)
(* Printing Sub-Protocol                                                      *)
(******************************************************************************)

(* Basically every function here should be an straightforward call to
 * Coq's printing. Coq bug if that is not the case.
 *)
let pp_goal_gen pr_c { Serapi_goals.ty ; hyp ; _ } =
  let open Pp      in
  let pr_idl idl = prlist_with_sep (fun () -> str ", ") Names.Id.print idl in
  let pr_lconstr_opt c = str " := " ++ pr_c c in
  let pr_hdef  = Option.cata pr_lconstr_opt (mt ())  in
  let pr_hyp (idl, hdef, htyp) =
    pr_idl idl ++ pr_hdef hdef ++ (str " : ") ++ pr_c htyp in
  pr_vertical_list pr_hyp hyp          ++
  str "============================\n" ++
    (* (let pr_lconstr t = *)
    (*    let (sigma, env) = Pfedit.get_current_context ()                            in *)
    (*    Ppconstr.Richpp.pr_lconstr_expr (Constrextern.extern_constr false env sigma t) *)
    (*  in *)
       pr_c ty

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

(*
let pp_richpp xml =
  let open Xml_datatype in
  let buf = Buffer.create 1024 in
  let rec print = function
  | PCData s -> Buffer.add_string buf s
  | Element (_, _, cs) -> List.iter print cs
  in
  let () = print xml in
  Buffer.contents buf
*)

let gen_pp_obj (obj : coq_object) : Pp.std_ppcmds =
  match obj with
  | CoqString  s    -> Pp.str s
  | CoqSList   s    -> Pp.(pr_sequence str) s
  | CoqPp      s    -> s
  (* | CoqRichpp  s    -> Pp.str (pp_richpp s) *)
  | CoqLoc    _loc  -> Pp.mt ()
  | CoqAst (_l, v)  -> Ppvernac.pr_vernac v
  | CoqMInd(m,mind) -> Printmod.pr_mutual_inductive_body (Global.env ()) m mind
  | CoqOption (n,s) -> pp_opt n s
  | CoqConstr  c    -> Printer.pr_lconstr c
  | CoqExpr    e    -> Ppconstr.pr_lconstr_expr e
  | CoqTactic(kn,_) -> Names.KerName.print kn
  (* Fixme *)
  | CoqGoal    g    -> Pp.pr_sequence (pp_goal_gen Printer.pr_lconstr)       g.Proof.fg_goals
  | CoqExtGoal g    -> Pp.pr_sequence (pp_goal_gen Ppconstr.pr_lconstr_expr) g.Proof.fg_goals
  | CoqProof  _     -> Pp.str "FIXME UPSTREAM, provide pr_proof"
  | CoqProfData _pf -> Pp.str "FIXME UPSTREAM, provide pr_prof_results"
  | CoqQualId qid   -> Pp.str (Libnames.string_of_qualid qid)
  | CoqGlobRef _gr  -> Pp.str "FIXME GlobRef"
  | CoqImplicit(_,l)-> Pp.pr_sequence pp_implicit l
  | CoqNotation ntn -> Pp.str ntn
  | CoqUnparsing _  -> Pp.str "FIXME Unparsing"

  (* | CoqPhyLoc(_,_,s)-> pr (Pp.str s) *)
  (* | CoqGoal (_,g,_) -> pr (Ppconstr.pr_lconstr_expr g) *)
  (* | CoqGlob   g -> pr (Printer.pr_glob_constr g) *)

(* XXX: This is terrible, but useful *)
let rec pp_opt (d : Pp.t) = let open Pp in
  let rec flatten_glue l = match l with
    | []  -> []
    | (Ppcmd_glue g :: l) -> flatten_glue (List.map repr g @ flatten_glue l)
    | (Ppcmd_string s1 :: Ppcmd_string s2 :: l) -> flatten_glue (Ppcmd_string (s1 ^ s2) :: flatten_glue l)
    | (x :: l) -> x :: flatten_glue l
  in
  (* let rec flatten_glue l = match l with *)
  (*   | (Ppcmd_string s1 :: Ppcmd_string s2 :: l) -> Ppcmd_string (s1 ^ s2) :: flatten_glue l *)
  unrepr (match repr d with
      | Ppcmd_glue []   -> Ppcmd_empty
      | Ppcmd_glue [x]  -> repr (pp_opt x)
      | Ppcmd_glue l    -> Ppcmd_glue List.(map pp_opt (map unrepr (flatten_glue (map repr l))))
      | Ppcmd_box(bt,d) -> Ppcmd_box(bt, pp_opt d)
      | Ppcmd_tag(t, d) -> Ppcmd_tag(t,  pp_opt d)
      | d -> d
    )

(* Enable to optimize *)
(* let gen_pp_obj obj : Pp.t = *)
(*   pp_opt (gen_pp_obj obj) *)

let _ = pp_opt

let str_pp_obj fmt (obj : coq_object)  =
  Format.fprintf fmt "%a" Pp.pp_with (gen_pp_obj obj)

(** Print output format  *)
type print_format =
  | PpSer
  | PpStr
  | PpTex
  | PpCoq
  (* | PpRichpp *)

(* register printer *)

type print_opt = {
  pp_format : print_format  [@default PpStr];
  pp_depth  : int           [@default 0];
  pp_elide  : string        [@default "..."];
  pp_margin : int           [@default 72];
}

let pp_tex (obj : coq_object) =
  let tex_sexp c = let open Format in
    pp_set_margin     str_formatter 300;
    pp_set_max_indent str_formatter 300;
    Stexp.pp_sexp_to_tex str_formatter c;
    flush_str_formatter ()
  in
  let open List           in
  let open Proof          in
  let open Ser_constr     in
  let open Ser_constrexpr in
  let open Serapi_goals   in
  match obj with
  | CoqConstr cst -> sexp_of_constr      cst |> tex_sexp
  | CoqGoal    gl -> let cst = (hd gl.fg_goals).ty in
                     sexp_of_constr      cst |> tex_sexp
  | CoqExtGoal gl -> let cst = (hd gl.fg_goals).ty in
                     sexp_of_constr_expr cst |> tex_sexp
  | _             -> "not supported"

let obj_print pr_opt obj =
  let open Format in
  match pr_opt.pp_format with
  | PpSer    -> obj
  | PpCoq    -> CoqPp (gen_pp_obj obj)
  | PpTex    -> CoqString (pp_tex obj)
  (* | PpRichpp -> CoqRichpp (Richpp.richpp_of_pp pr_opt.pp_margin (gen_pp_obj obj)) *)
  | PpStr ->
    let mb      = pp_get_max_boxes     str_formatter () in
    let et      = pp_get_ellipsis_text str_formatter () in
    let mg      = pp_get_margin        str_formatter () in
    pp_set_max_boxes     str_formatter pr_opt.pp_depth;
    pp_set_ellipsis_text str_formatter pr_opt.pp_elide;
    pp_set_margin        str_formatter pr_opt.pp_margin;

    fprintf str_formatter "@[%a@]" str_pp_obj obj;
    let str_obj = CoqString (flush_str_formatter ())    in

    pp_set_max_boxes     str_formatter mb;
    pp_set_ellipsis_text str_formatter et;
    pp_set_margin        str_formatter mg;
    str_obj

(******************************************************************************)
(* Answer Types                                                               *)
(******************************************************************************)

(* XXX: Fixme: adapt to 4.03 matching? *)
type answer_kind =
    Ack
  | Completed
  | Added     of Stateid.t * Loc.t * [`NewTip | `Unfocus of Stateid.t ]
  | Canceled  of Stateid.t list
  | ObjList   of coq_object list
  | CoqExn    of Loc.t option * (Stateid.t * Stateid.t) option * exn

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
  | CoqLoc     _    -> true
  | CoqPp      _    -> true
  (* | CoqRichpp  _    -> true *)
  | CoqAst     _    -> true
  | CoqOption (n,_) -> Extra.is_prefix (String.concat "." n) ~prefix
  | CoqConstr _     -> true
  | CoqExpr _       -> true
  | CoqMInd _       -> true
  | CoqTactic(kn,_) -> Extra.is_prefix (Names.KerName.to_string kn) ~prefix
  (* | CoqPhyLoc _     -> true *)
  | CoqQualId _     -> true
  | CoqGlobRef _    -> true
  | CoqProfData _   -> true
  | CoqImplicit _   -> true
  | CoqGoal _       -> true
  | CoqNotation _   -> true
  | CoqUnparsing _  -> true
  | CoqExtGoal _    -> true
  | CoqProof _      -> true

let gen_pred (p : query_pred) (obj : coq_object) : bool = match p with
  | Prefix s -> prefix_pred s obj

type query_opt =
  { preds : query_pred sexp_list;
    limit : int sexp_option;
    sid   : Stateid.t [@default Stm.get_current_state()];
    pp    : print_opt [@default { pp_format = PpSer; pp_depth = 0; pp_elide = "..."; pp_margin = 72 } ];
    (* Legacy/Deprecated *)
    route : Feedback.route_id [@default 0];
  }

(** XXX: This should be in sync with the object tag!  *)
type query_cmd =
  | Option   (*  *)
  | Search                         (* Search vernacular, we only support prefix by name *)
  | Goals                          (* Return goals [TODO: Add filtering/limiting options] *)
  | EGoals                         (* Return goals [TODO: Add filtering/limiting options] *)
  | Ast        of Stateid.t        (* Return ast *)
  | TypeOf     of string
  | Names      of string           (* XXX Move to prefix *)
  | Tactics    of string           (* XXX Print LTAC signatures (with prefix) *)
  | Locate     of string           (* XXX Print LTAC signatures (with prefix) *)
  | Implicits  of string           (* XXX Print LTAC signatures (with prefix) *)
  | Unparsing  of string           (* XXX  *)
  | Definition of string
  | PNotations                     (* XXX  *)
  | ProfileData
  | Proof                          (* Return the proof object *)
  | Vernac     of string           (* [legacy] Execute arbitrary Coq command in an isolated state. *)

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
  (* XXX: We need to put this into a plugin, as ltac is now a plugin in 8.7. *)
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

  let query_unparsing (nt : Constrexpr.notation) :
    Notation.unparsing_rule * Notation.extra_unparsing_rules * Notation_term.notation_grammar =
    Notation.(find_notation_printing_rule nt,
              find_notation_extra_printing_rules nt,
              find_notation_parsing_rules nt)

  let query_pnotations () =
    Notation.get_defined_notations ()

  let locate id =
    let open Names     in
    let open Libnames  in
    let open Globnames in
    (* From prettyp.ml *)
    let qid = qualid_of_string id in
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

  (* Copied from Coq. XXX *)
  let type_of_constant cb = match cb.Declarations.const_type with
    | Declarations.RegularArity ty -> ty
    | Declarations.TemplateArity (ctx, arity) ->
      Term.mkArity (ctx, Sorts.sort_of_univ arity.Declarations.template_level)

  (* Definition of an inductive *)
  let info_of_ind (sp, _) =
    [CoqMInd (sp, Global.lookup_mind sp)], []

  let info_of_const cr =
    let cdef = Global.lookup_constant cr in
    Option.cata (fun cb -> [CoqConstr cb] ) [] (Global.body_of_constant cr),
    [CoqConstr(type_of_constant cdef)]

  let info_of_var vr =
    let vdef = Global.lookup_named vr in
    Option.cata (fun cb -> [CoqConstr cb] ) [] (Context.Named.Declaration.get_value vdef),
    [CoqConstr(Context.Named.Declaration.get_type vdef)]

  (* XXX: Some work to do wrt Global.type_of_global_unsafe  *)
  let info_of_constructor cr =
    (* let cdef = Global.lookup_pinductive (cn, cu) in *)
    let ctype = Global.type_of_global_unsafe (Globnames.ConstructRef cr) in
    [],[CoqConstr ctype]

  (* Queries a generic definition, in the style of the `Print` vernacular *)
  (*                  definition        type                              *)
  let info_of_id id : coq_object list * coq_object list =
    (* parse to a qualified name                        *)
    let qid = Libnames.qualid_of_ident (Names.Id.of_string id) in
    (* try locate the kind of object the name refers to *)
    try
      let lid = Nametab.locate qid in
      (* dispatch based on type *)
      let open Globnames in
      match lid with
      | VarRef        vr -> info_of_var vr
      | ConstRef      cr -> info_of_const cr
      | IndRef        ir -> info_of_ind ir
      | ConstructRef  cr -> info_of_constructor cr
    with _ -> [],[]

end

let obj_query (opt : query_opt) (cmd : query_cmd) : coq_object list =
  match cmd with
  | Option         -> let table = Goptions.get_tables ()            in
                      let opts  = Goptions.OptionMap.bindings table in
                      List.map (fun (n,s) -> CoqOption(n,s)) opts
  | Goals          -> Option.cata (fun g -> [CoqGoal g   ]) [] @@ Serapi_goals.get_goals  opt.sid
  | EGoals         -> Option.cata (fun g -> [CoqExtGoal g]) [] @@ Serapi_goals.get_egoals opt.sid
  | Ast sid        -> Option.cata (fun last -> [CoqAst last]) [] @@ Stm.get_ast sid
  | Names   prefix -> QueryUtil.query_names_locate prefix
  | Tactics prefix -> List.map (fun (i,t) -> CoqTactic(i,t)) @@ QueryUtil.query_tactics prefix
  | Locate  id     -> List.map (fun qid -> CoqQualId qid) @@ QueryUtil.locate id
  | Implicits id   -> List.map (fun ii -> CoqImplicit ii ) @@ QueryUtil.implicits id
  | ProfileData    -> [CoqProfData (Profile_ltac.get_local_profiling_results ())]
  | Proof          -> begin
                        try
                          let (a,b,c,d,_) = Proof.proof (Proof_global.give_me_the_proof ()) in
                          [CoqProof (a,b,c,d)]
                        with Proof_global.NoCurrentProof -> []
                      end
  | Unparsing ntn  -> (* Unfortunately this will produce an anomaly if the notation is not found...
                       * To keep protocol promises we need to special wrap it.
                       *)
                      begin try let up, upe, gr = QueryUtil.query_unparsing ntn in
                                [CoqUnparsing(up,upe,gr)]
                      with _exn -> []
                      end
  | PNotations     -> List.map (fun s -> CoqNotation s) @@ QueryUtil.query_pnotations ()
  | Definition id  -> fst (QueryUtil.info_of_id id)
  | TypeOf id      -> snd (QueryUtil.info_of_id id)
  | Search         -> [CoqString "Not Implemented"]
  (* XXX: should set printing options in all queries *)
  | Vernac q       -> let pa = Pcoq.Gram.parsable (Stream.of_string q) in
                      Stm.query ~at:opt.sid ~route:opt.route pa; []

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

(* XXX: Need to protect queries... sad *)
let exec_query opt cmd =
  let res = obj_query opt cmd        in
  (* XXX: Filter should move to query once we have GADT *)
  let res = obj_filter opt.preds res in
  let res = obj_limit  opt.limit res in
  List.map (obj_print opt.pp) res

(******************************************************************************)
(* Control Sub-Protocol                                                       *)
(******************************************************************************)

(* coq_exn info *)
let coq_exn_info exn =
    let (e, info) = CErrors.push exn in
    CoqExn (Loc.get_loc info, Stateid.get info, e)

(* Simple protection for Coq-generated exceptions *)
let coq_protect e =
  try  e () @ [Completed]
  with exn -> [coq_exn_info exn]
    (* let msg = str msg ++ fnl () ++ CErrors.print ~info e in *)
    (* Richpp.richpp_of_pp msg *)

type add_opts = {
  lim    : int       sexp_option;
  ontop  : Stateid.t sexp_option;
  newtip : Stateid.t sexp_option;
  verb   : bool      [@default false];
}

let exec_setopt loc n (v : Goptions.option_value) =
  let open Goptions in
  match v with
  | BoolValue b      -> set_bool_option_value_gen loc n b
  | IntValue  i      -> set_int_option_value_gen  loc n i
  | StringValue s    -> set_string_option_value_gen loc n s
  | StringOptValue s -> set_string_option_value_gen loc n (Option.default "" s)

module ControlUtil = struct

  type doc    = Stateid.t list
  let cur_doc : doc ref = ref [Stateid.of_int 1]

  let pp_doc fmt l =
    let open Serapi_pp in
    Format.fprintf fmt "@[%a@]" (pp_list ~sep:" " pp_stateid) l

  let _dump_doc () =
    Format.eprintf "%a@\n%!" pp_doc !cur_doc

  let add_sentences opts sent =
    let pa = Pcoq.Gram.parsable (Stream.of_string sent) in
    let i   = ref 1                    in
    let acc = ref []                   in
    let stt = ref (Extra.value opts.ontop ~default:(Stm.get_current_state ())) in
    let check_lim i = Extra.value_map opts.lim ~default:true ~f:(fun lim -> i <= lim) in
    try
      while check_lim !i do
        (* XXX: We check that the ontop state is actually in the
         * document to avoid an Anomaly exception.
         *)
        if not (List.mem !stt !cur_doc) then
          raise (NoSuchState !stt);
        let east      = Stm.parse_sentence !stt pa in
        (* XXX: Must like refine the API *)
        let eloc      = Option.get (fst east)      in
        let n_st, foc = Stm.add ?newtip:opts.newtip ~ontop:!stt opts.verb east in
        cur_doc := n_st :: !cur_doc;
        acc := (Added (n_st, eloc, foc)) :: !acc;
        stt := n_st;
        incr i
      done;
      List.rev !acc
    with
    | Stm.End_of_input -> List.rev !acc
    | exn              -> List.rev (coq_exn_info exn :: !acc)

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
                 [Canceled c_ran]
    (* - [tip] is the new document tip.
       - [st]   -- [stop] is dropped.
       - [stop] -- [tip]  has been kept.
       - [start] is where the editing zone starts
       - [add] happen on top of [id].
    *)
    | `Focus foc -> cancel_interval can_st foc

end

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
  | Add        of add_opts  * string
  | Cancel     of Stateid.t list
  | Exec       of Stateid.t
  | Query      of query_opt * query_cmd
  | Print      of print_opt * coq_object
  (* Full document checking *)
  | Join
  (*******************************************************************)
  (* XXX: We want to have query / update and fuse these two under it *)
  (*              coq_path      unix_path   has_ml                   *)
  | LibAdd     of string list * string    * bool
  (* Miscellanous *)
  | SetOpt     of bool option * Goptions.option_name * Goptions.option_value
  (*******************************************************************)
  (* Non-supported command, only for convenience. *)
  | ReadFile   of string
  | Noop
  | Help
  | Quit


let exec_cmd (cmd : cmd) =
  coq_protect @@ fun () -> match cmd with
  | Add (opt, s) -> ControlUtil.add_sentences opt s
  | Cancel st    -> List.concat @@ List.map ControlUtil.cancel_sentence st
  | Exec st      -> Stm.observe st; []
  | Query (opt, qry)  -> [ObjList (exec_query opt qry)]
  | Print(opts, obj)  -> [ObjList [obj_print opts obj]]
  | Join              -> Stm.join (); []

  (*******************************************************************)
  | LibAdd(lib, lib_path, has_ml) ->
    let open Names in
    let coq_path = DirPath.make @@ List.rev @@ List.map Names.Id.of_string lib in
    (* XXX [upstream]: Unify ML and .vo library paths.  *)
    Loadpath.add_load_path lib_path coq_path ~implicit:false;
    if has_ml then Mltop.add_ml_dir lib_path;
    []

  | SetOpt(loc, n, v) -> exec_setopt loc n v; []
  (*******************************************************************)
  | ReadFile f ->
    Pervasives.(
      let inc = open_in f in
      try
        let faddopts = { lim = None; ontop = None; newtip = None; verb = false; } in
        let fsize    = in_channel_length inc         in
        let fcontent = really_input_string inc fsize in
        ControlUtil.add_sentences faddopts fcontent
      with _ -> close_in inc; []
    )
  | Help           -> serproto_help (); []
  | Noop           -> []
  | Quit           -> []

type cmd_tag    = string
type tagged_cmd = cmd_tag * cmd

type answer =
  | Answer    of cmd_tag * answer_kind
  | Feedback  of Feedback.feedback

