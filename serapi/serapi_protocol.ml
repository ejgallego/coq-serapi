(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
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
open! Sexplib.Conv

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

  let rec stream_tok n_tok acc (str,loc_fn) =
    let e = Stream.next str in
    let loc = loc_fn n_tok in
    let l_tok = CAst.make ~loc e in
    if Tok.(equal e EOI) then
      List.rev (l_tok::acc)
    else
      stream_tok (n_tok+1) (l_tok::acc) (str,loc_fn)

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
  | CoqTok       of Tok.t CAst.t list
  | CoqAst       of Vernacexpr.vernac_control
  | CoqOption    of Goptions.option_name * Goptions.option_state
  | CoqConstr    of Constr.constr
  | CoqExpr      of Constrexpr.constr_expr
  | CoqMInd      of Names.MutInd.t * Declarations.mutual_inductive_body
  | CoqEnv       of Environ.env
  | CoqTactic    of Names.KerName.t * Tacenv.ltac_entry
  | CoqLtac      of Tacexpr.raw_tactic_expr
  | CoqGenArg    of Genarg.raw_generic_argument
  | CoqQualId    of Libnames.qualid
  | CoqGlobRef   of Names.GlobRef.t
  | CoqGlobRefExt of Globnames.extended_global_reference
  | CoqImplicit  of Impargs.implicits_list
  | CoqProfData  of Profile_ltac.treenode
  | CoqNotation  of Constrexpr.notation
  | CoqUnparsing of Ppextend.unparsing_rule * Ppextend.extra_unparsing_rules * Notation_gram.notation_grammar
  | CoqGoal      of Constr.t               Serapi_goals.reified_goal Serapi_goals.ser_goals
  | CoqExtGoal   of Constrexpr.constr_expr Serapi_goals.reified_goal Serapi_goals.ser_goals
  | CoqProof     of Goal.goal list
                    * (Goal.goal list * Goal.goal list) list
                    (* We don't seralize the evar map for now... *)
                    (* * Evd.evar_map *)
  | CoqAssumptions of Serapi_assumptions.t
  | CoqComments of ((int * int) * string) list list

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

let pp_explicitation = let open Constrexpr in function
  | ExplByPos (i, None) -> Pp.(int i ++ str "None")
  | ExplByPos (i, Some iname) -> Pp.(int i ++ Names.Id.print iname)
  | ExplByName iname -> Names.Id.print iname

let pp_implicit : Impargs.implicit_status -> Pp.t = function
  | None              -> Pp.str "!"
  | Some (expl, _, _) -> pp_explicitation expl

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

let gen_pp_obj env sigma (obj : coq_object) : Pp.t =
  match obj with
  | CoqString  s    -> Pp.str s
  | CoqSList   s    -> Pp.(pr_sequence str) s
  | CoqPp      s    -> s
  (* | CoqRichpp  s    -> Pp.str (pp_richpp s) *)
  | CoqLoc    _loc  -> Pp.mt ()
  | CoqTok    toks  -> Pp.pr_sequence (fun {CAst.v = tok;_} -> Pp.str (Tok.(extract_string false tok))) toks
  | CoqAst v        -> Ppvernac.pr_vernac v
  | CoqMInd(m,mind) -> Printmod.pr_mutual_inductive_body env m mind None
  | CoqOption (n,s) -> pp_opt n s
  | CoqConstr  c    -> Printer.pr_lconstr_env env sigma c
  | CoqExpr    e    -> Ppconstr.pr_lconstr_expr env sigma e
  | CoqEnv _env     -> Pp.str "Cannot pretty print environments"
  | CoqTactic(kn,_) -> Names.KerName.print kn
  | CoqLtac t       -> Pptactic.pr_raw_tactic env sigma t
  | CoqGenArg ga    ->
    let open Genprint in
    begin match generic_raw_print ga with
      | PrinterBasic pp -> pp env sigma
      (* XXX: Fixme, the level here is random *)
      | PrinterNeedsLevel pp ->
        pp.printer env sigma Constrexpr.LevelSome
    end

  (* Fixme *)
  | CoqGoal    g    -> Pp.pr_sequence (pp_goal_gen Printer.(pr_lconstr_env env sigma)) g.Serapi_goals.goals
  | CoqExtGoal g    -> Pp.pr_sequence (pp_goal_gen Ppconstr.(pr_lconstr_expr env sigma)) g.Serapi_goals.goals
  | CoqProof  _     -> Pp.str "FIXME UPSTREAM, provide pr_proof"
  | CoqProfData _pf -> Pp.str "FIXME UPSTREAM, provide pr_prof_results"
  | CoqQualId qid   -> Pp.str (Libnames.string_of_qualid qid)
  | CoqGlobRef gr   -> Printer.pr_global gr
  | CoqGlobRefExt gr ->
    (match gr with
     | Globnames.TrueGlobal gr -> Printer.pr_global gr
     | Globnames.SynDef kn -> Names.KerName.print kn
    )
  | CoqImplicit(_,l) -> Pp.pr_sequence pp_implicit l
  | CoqNotation ntn  -> Pp.str (snd ntn)
  | CoqUnparsing _   -> Pp.str "FIXME Unparsing"
  | CoqAssumptions a -> Serapi_assumptions.print env sigma a
  (* | CoqPhyLoc(_,_,s)-> pr (Pp.str s) *)
  (* | CoqGoal (_,g,_) -> pr (Ppconstr.pr_lconstr_expr g) *)
  (* | CoqGlob   g -> pr (Printer.pr_glob_constr g) *)
  | CoqComments _ -> Pp.str "FIXME comments"

let str_pp_obj env sigma fmt (obj : coq_object)  =
  Format.fprintf fmt "%a" Pp.pp_with (gen_pp_obj env sigma obj)

(** Print output format  *)
type print_format =
  | PpSer
  (** Output in serialized format [usually sexp but could be extended in the future] *)
  | PpStr
  (** Output a string with a human-friendly representation *)
  | PpTex
  (** Output a TeX expression *)
  | PpCoq
  (** Output a TeX expression *)
  (* | PpRichpp *)

(* register printer *)

type format_opt = {
  pp_format : print_format  [@default PpSer];
  pp_depth  : int           [@default 0];
  pp_elide  : string        [@default "..."];
  pp_margin : int           [@default 72];
}

type print_opt =
  { sid   : Stateid.t [@default Stm.get_current_state ~doc:Stm.(get_doc 0)];
    (** [sid] denotes the {e sentence id} we are querying over, essential information as goals for example will vary. *)
    pp    : format_opt [@default { pp_format = PpSer; pp_depth = 0; pp_elide = "..."; pp_margin = 72 } ];
    (** Printing format of the query, this can be used to select the type of the answer, as for example to show goals in human-form. *)
  }

let pp_tex (_obj : coq_object) = ""
(*
  let tex_sexp c = let open Format in
    pp_set_margin     str_formatter 300;
    pp_set_max_indent str_formatter 300;
    Stexp.pp_sexp_to_tex str_formatter c;
    flush_str_formatter ()
  in
  let open List           in
  let open Ser_constr     in
  let open Ser_constrexpr in
  let open Ser_vernacexpr in
  let open Serapi_goals   in
  match obj with
  | CoqConstr cst -> sexp_of_constr      cst |> tex_sexp
  | CoqGoal    gl -> let cst = (hd gl.goals).ty in
                     sexp_of_constr      cst |> tex_sexp
  | CoqExtGoal gl -> let cst = (hd gl.goals).ty in
                     sexp_of_constr_expr cst |> tex_sexp
  | CoqAst(_,ast) -> sexp_of_vernac_control ast |> tex_sexp
  | _             -> "not supported"
*)

let obj_print env sigma pr_opt obj =
  let open Format in
  match pr_opt.pp_format with
  | PpSer    -> obj
  | PpCoq    -> CoqPp (gen_pp_obj env sigma obj)
  | PpTex    -> CoqString (pp_tex obj)
  (* | PpRichpp -> CoqRichpp (Richpp.richpp_of_pp pr_opt.pp_margin (gen_pp_obj obj)) *)
  | PpStr ->
    let mb      = pp_get_max_boxes     str_formatter () in
    let et      = pp_get_ellipsis_text str_formatter () in
    let mg      = pp_get_margin        str_formatter () in
    pp_set_max_boxes     str_formatter pr_opt.pp_depth;
    pp_set_ellipsis_text str_formatter pr_opt.pp_elide;
    pp_set_margin        str_formatter pr_opt.pp_margin;

    fprintf str_formatter "@[%a@]" (str_pp_obj env sigma) obj;
    let str_obj = CoqString (flush_str_formatter ())    in

    pp_set_max_boxes     str_formatter mb;
    pp_set_ellipsis_text str_formatter et;
    pp_set_margin        str_formatter mg;
    str_obj

(******************************************************************************)
(* Answer Types                                                               *)
(******************************************************************************)

module ExnInfo = struct
  type t =
    { loc : Loc.t option
    ; stm_ids : (Stateid.t * Stateid.t) option
    ; backtrace : Printexc.raw_backtrace
    ; exn : exn
    ; pp : Pp.t
    ; str : string
    }
end

(* XXX: Fixme: adapt to 4.03 matching? *)
type answer_kind =
    Ack
  | Completed
  | Added     of Stateid.t * Loc.t * [`NewTip | `Unfocus of Stateid.t ]
  | Canceled  of Stateid.t list
  | ObjList   of coq_object list
  | CoqExn    of ExnInfo.t

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
  | CoqTok     _    -> true
  | CoqPp      _    -> true
  (* | CoqRichpp  _    -> true *)
  | CoqAst     _    -> true
  | CoqOption (n,_) -> Extra.is_prefix (String.concat "." n) ~prefix
  | CoqConstr _     -> true
  | CoqExpr _       -> true
  | CoqMInd _       -> true
  | CoqEnv _        -> true
  | CoqTactic(kn,_) -> Extra.is_prefix (Names.KerName.to_string kn) ~prefix
  | CoqLtac _       -> true
  | CoqGenArg _     -> true
  (* | CoqPhyLoc _     -> true *)
  | CoqQualId _     -> true
  | CoqGlobRef _    -> true
  | CoqGlobRefExt _ -> true
  | CoqProfData _   -> true
  | CoqImplicit _   -> true
  | CoqGoal _       -> true
  | CoqNotation _   -> true
  | CoqUnparsing _  -> true
  | CoqExtGoal _    -> true
  | CoqProof _      -> true
  | CoqAssumptions _-> true
  | CoqComments _   -> true

let gen_pred (p : query_pred) (obj : coq_object) : bool = match p with
  | Prefix s -> prefix_pred s obj

type query_opt =
  { preds : query_pred list [@sexp.list];
    limit : int option [@sexp.option];
    sid   : Stateid.t [@default Stm.get_current_state()];
    pp    : format_opt [@default { pp_format = PpSer; pp_depth = 0; pp_elide = "..."; pp_margin = 72 } ];
    (* Legacy/Deprecated *)
    route : Feedback.route_id [@default 0];
  }

(** XXX: This should be in sync with the object tag!  *)
type query_cmd =
  | Option   (*  *)
  | Search                         (* Search vernacular, we only support prefix by name *)
  | Goals                          (* Return goals [TODO: Add filtering/limiting options] *)
  | EGoals                         (* Return goals [TODO: Add filtering/limiting options] *)
  | Ast                            (* Return ast *)
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
  | Env                            (* Return the current global enviroment *)
  | Assumptions of string          (* Return the assumptions of given identifier *)
  | Complete of string
  | Comments
  (** Get all comments of a document *)

module QueryUtil = struct

  let _query_names prefix =
    let acc = ref [] in
    let env = Global.env () in
    Search.generic_search env (fun gr _kind _env _typ ->
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
            (Libnames.string_of_qualid (Tacenv.shortest_qualid_of_tactic kn)) ~prefix
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
    Ppextend.unparsing_rule * Ppextend.extra_unparsing_rules * Notation_gram.notation_grammar =
    Ppextend.find_notation_printing_rule None nt,
    Ppextend.find_notation_extra_printing_rules None nt,
    Notgram_ops.grammar_of_notation nt

  let query_pnotations () =
    Notgram_ops.get_defined_notations ()

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
  let type_of_constant cb = cb.Declarations.const_type

  (* Definition of an inductive *)
  let info_of_ind env (sp, _) =
    [CoqMInd (sp, Environ.lookup_mind sp env)], []

  let info_of_const env cr =
    let cdef = Environ.lookup_constant cr env in
    let cb = Environ.lookup_constant cr env in
    Option.cata (fun (cb,_univs,_uctx) -> [CoqConstr cb] ) []
      (Global.body_of_constant_body Library.indirect_accessor cb),
    [CoqConstr(type_of_constant cdef)]

  let info_of_var env vr =
    let vdef = Environ.lookup_named vr env in
    Option.cata (fun cb -> [CoqConstr cb] ) [] (Context.Named.Declaration.get_value vdef),
    [CoqConstr(Context.Named.Declaration.get_type vdef)]

  (* XXX: Some work to do wrt Global.type_of_global_unsafe  *)
  let info_of_constructor env cr =
    (* let cdef = Global.lookup_pinductive (cn, cu) in *)
    let (ctype, _uctx) = Typeops.type_of_global_in_context env (Names.GlobRef.ConstructRef cr) in
    [],[CoqConstr ctype]

  (* Queries a generic definition, in the style of the `Print` vernacular *)
  (*                  definition        type                              *)
  let info_of_id env id : coq_object list * coq_object list =
    (* parse string to a qualified name                 *)
    let qid = Libnames.qualid_of_string id in
    (* try locate the kind of object the name refers to *)
    try
      let lid = Nametab.locate qid in
      (* dispatch based on type *)
      let open Names.GlobRef in
      match lid with
      | VarRef        vr -> info_of_var env vr
      | ConstRef      cr -> info_of_const env cr
      | IndRef        ir -> info_of_ind env ir
      | ConstructRef  cr -> info_of_constructor env cr
    with _ -> [],[]

  let assumptions env id =

    let qid = Libnames.qualid_of_string id in

    let smart_global r =
      let gr = Nametab.locate r in
      Dumpglob.add_glob ?loc:r.loc gr;
      gr
    in
    let gr = smart_global qid in
    let cstr = Globnames.printable_constr_of_global gr in
    let st = Conv_oracle.get_transp_state (Environ.oracle env) in
    let nassums =
      Assumptions.assumptions st ~add_opaque:true ~add_transparent:true gr cstr in
    Serapi_assumptions.build env nassums

  (* This should be moved Coq upstream *)
  let _comments = ref []
  let add_comments pa =
    let comments = Pcoq.Parsable.comments pa |> List.rev in
    _comments := comments :: !_comments

end

let obj_query ~doc ~pstate ~env (opt : query_opt) (cmd : query_cmd) : coq_object list =
  match cmd with
  | Option         -> let table = Goptions.get_tables ()            in
                      let opts  = Goptions.OptionMap.bindings table in
                      List.map (fun (n,s) -> CoqOption(n,s)) opts
  | Goals          -> Option.cata (fun g -> [CoqGoal g   ]) [] @@ Serapi_goals.get_goals  ~doc opt.sid
  | EGoals         -> Option.cata (fun g -> [CoqExtGoal g]) [] @@ Serapi_goals.get_egoals ~doc opt.sid
  | Ast            -> Option.cata (fun last -> [CoqAst last]) [] @@ Stm.get_ast ~doc opt.sid
  | Names   prefix -> QueryUtil.query_names_locate prefix
  | Tactics prefix -> List.map (fun (i,t) -> CoqTactic(i,t)) @@ QueryUtil.query_tactics prefix
  | Locate  id     -> List.map (fun qid -> CoqQualId qid) @@ QueryUtil.locate id
  | Implicits id   -> List.map (fun ii -> CoqImplicit ii ) @@ QueryUtil.implicits id
  | ProfileData    -> [CoqProfData (Profile_ltac.get_local_profiling_results ())]
  | Proof          -> Option.cata (fun pstate ->
                        let Proof.{goals; stack; _} =
                          Proof.data (Declare.Proof.get pstate) in
                        [CoqProof (goals,stack)])
                      [] pstate
  | Unparsing ntn  -> (* Unfortunately this will produce an anomaly if the notation is not found...
                       * To keep protocol promises we need to special wrap it.
                       *)
                      begin try let up, upe, gr = QueryUtil.query_unparsing (Constrexpr.InConstrEntry,ntn) in
                                [CoqUnparsing(up,upe,gr)]
                      with _exn -> []
                      end
  | PNotations     -> List.map (fun s -> CoqNotation s) @@ QueryUtil.query_pnotations ()
  | Definition id  -> fst (QueryUtil.info_of_id env id)
  | TypeOf id      -> snd (QueryUtil.info_of_id env id)
  | Search         -> [CoqString "Not Implemented"]
  (* XXX: should set printing options in all queries *)
  | Vernac q       -> let pa = Pcoq.Parsable.make (Stream.of_string q) in
                      Stm.query ~doc ~at:opt.sid ~route:opt.route pa; []
  (* XXX: Should set the proper sid state *)
  | Env            -> [CoqEnv env]
  | Assumptions id ->
    [CoqAssumptions QueryUtil.(assumptions env id)]
  | Complete prefix ->
    List.map (fun x -> CoqGlobRefExt x) (Nametab.completion_canditates (Libnames.qualid_of_string prefix))
  | Comments -> [CoqComments (List.rev !QueryUtil._comments)]

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
let doc_id = ref 0

(* XXX: Needs to take into account possibly local proof state *)
let pstate_of_st m = match m with
  | `Valid (Some { Vernacstate.lemmas; _ } ) ->
    Option.map (Vernacstate.LemmaStack.with_top ~f:(fun p -> p)) lemmas
  | _ -> None

let context_of_st m = match m with
  | `Valid (Some { Vernacstate.lemmas = Some lemma; _ } ) ->
    Vernacstate.LemmaStack.with_top lemma
      ~f:(fun p -> Declare.Proof.get_current_context p)
    (* let pstate = st.Vernacstate.proof in *)
    (* let summary = States.summary_of_state st.Vernacstate.system in
     * Safe_typing.env_of_safe_env Summary.(project_from_summary summary Global.global_env_summary_tag) *)
  | _ ->
    let env = Global.env () in Evd.from_env env, env

let exec_query opt cmd =
  let doc = Stm.get_doc !doc_id in
  let st = Stm.state_of_id ~doc opt.sid in
  let sigma, env = context_of_st st in
  let pstate = pstate_of_st st in

  let res = obj_query ~doc ~pstate ~env opt cmd in
  (* XXX: Filter should move to query once we have GADT *)
  let res = obj_filter opt.preds res in
  let res = obj_limit  opt.limit res in
  List.map ((obj_print env sigma) opt.pp) res

(******************************************************************************)
(* Control Sub-Protocol                                                       *)
(******************************************************************************)

(* coq_exn info *)
let coq_exn_info exn =
  let backtrace = Printexc.get_raw_backtrace () in
  let exn, info = Exninfo.capture exn in
  let pp = CErrors.iprint (exn, info) in
  CoqExn
    { loc = Loc.get_loc info
    ; stm_ids = Stateid.get info
    ; backtrace
    ; exn
    ; pp
    ; str = Pp.string_of_ppcmds pp
    }

(* Simple protection for Coq-generated exceptions *)
let coq_protect e =
  try  e () @ [Completed]
  with exn -> [coq_exn_info exn; Completed]
    (* let msg = str msg ++ fnl () ++ CErrors.print ~info e in *)
    (* Richpp.richpp_of_pp msg *)

type parse_opt =
  { ontop  : Stateid.t option [@sexp.option] }

type add_opts = {
  lim    : int       option [@sexp.option];
  ontop  : Stateid.t option [@sexp.option];
  newtip : Stateid.t option [@sexp.option];
  verb   : bool      [@default false];
}

module ControlUtil = struct

  type doc    = Stateid.t list
  let cur_doc : doc ref = ref [Stateid.of_int 1]

  let pp_doc fmt l =
    let open Serapi_pp in
    Format.fprintf fmt "@[%a@]" (pp_list ~sep:" " pp_stateid) l

  let _dump_doc () =
    Format.eprintf "%a@\n%!" pp_doc !cur_doc

  let parse_sentence ~doc ~(opt : parse_opt) sent =
    let ontop = Extra.value opt.ontop ~default:(Stm.get_current_state ~doc) in
    let pa = Pcoq.Parsable.make (Stream.of_string sent) in
    let entry = Pvernac.main_entry in
    Stm.parse_sentence ~doc ontop ~entry pa

  exception End_of_input

  let add_sentences ~doc opts sent =
    let pa = Pcoq.Parsable.make (Stream.of_string sent) in
    let i   = ref 1                    in
    let acc = ref []                   in
    let stt = ref (Extra.value opts.ontop ~default:(Stm.get_current_state ~doc)) in
    let doc = ref doc                  in
    let check_lim i = Extra.value_map opts.lim ~default:true ~f:(fun lim -> i <= lim) in
    try
      while check_lim !i do
        (* XXX: We check that the ontop state is actually in the
         * document to avoid an Anomaly exception.
         *)
        if not (List.mem !stt !cur_doc) then
          raise (NoSuchState !stt);
        let east      =
          (* Flags.beautify is needed so comments are stored by the lexer... *)
          let parse_res =
            Flags.with_option Flags.beautify
              (Stm.parse_sentence ~doc:!doc !stt ~entry:Pvernac.main_entry) pa in
          match parse_res with
          | Some ast -> ast
          | None -> raise End_of_input
        in
        Flags.beautify := false;
        (* XXX: Must like refine the API *)
        let eloc      = Option.get (east.CAst.loc) in
        let n_doc, n_st, foc = Stm.add ~doc:!doc ?newtip:opts.newtip ~ontop:!stt opts.verb east in
        doc := n_doc;
        cur_doc := n_st :: !cur_doc;
        acc := (Added (n_st, eloc, foc)) :: !acc;
        stt := n_st;
        incr i
      done;
      !doc, pa, List.rev !acc
    with
    | End_of_input ->
      !doc, pa, List.rev !acc
    | exn          ->
      !doc, pa, List.rev (coq_exn_info exn :: !acc)

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

  let cancel_sentence ~doc can_st =
    (* dump_doc (); *)
    let c_ran, k_ran = invalid_range can_st ~incl:true in
    let prev_st      = Extra.value (Extra.hd_opt k_ran) ~default:Stateid.initial in
    match Stm.edit_at ~doc prev_st with
    | doc, `NewTip ->
      cur_doc := k_ran;
      doc, [Canceled c_ran]
    (* - [tip] is the new document tip.
       - [st]   -- [stop] is dropped.
       - [stop] -- [tip]  has been kept.
       - [start] is where the editing zone starts
       - [add] happen on top of [id].
    *)
    | doc, `Focus foc ->
      doc, cancel_interval can_st foc

end

(******************************************************************************)
(* Init / new document                                                        *)
(******************************************************************************)
type newdoc_opts =
  { top_name     : Stm.interactive_top
  (** name of the top-level module of the new document *)
  ; ml_load_path   : string list option [@sexp.option]
  (** Initial ML loadpath  *)
  ; vo_load_path   : Loadpath.vo_path list option [@sexp.option]
  (** Initial LoadPath for the document *) (* [XXX: Use the coq_pkg record?] *)
  ; require_libs : (string * string option * bool option) list option [@sexp.option]
  (** Libraries to load in the initial document state *)
  }

(******************************************************************************)
(* Help                                                                       *)
(******************************************************************************)

(* Prints help to stderr. TODO, we should use a ppx to automatically
   generate the description of the protocol. *)
let serproto_help () =
  let open Format in
  eprintf "%s%!"
    ("Coq SerAPI -- Protocol documentation is still incomplete, the main commands are: \n\n" ^
     "  (Add add_opt \"gallina code\") -- Add new sentences to the current document \n"      ^
     "  (Cancel sid_list)            -- Cancel sentences in the current document \n"         ^
     "  (Exec sid)                   -- Check sentence `sid` \n"                             ^
     "  (Query query_opt query_cmd)  -- Query information about a sentence / global data \n" ^
     "  (Print print_opt coq_object) -- Print object with options \n"                        ^
     "\nSee sertop_protocol.mli for more details.\n\n")

(******************************************************************************)
(* Top-Level Commands                                                         *)
(******************************************************************************)

type cmd =
  | NewDoc     of newdoc_opts
  | Add        of add_opts  * string
  | Cancel     of Stateid.t list
  | Exec       of Stateid.t
  | Query      of query_opt * query_cmd
  | Print      of print_opt * coq_object
  | Parse      of parse_opt * string
  (* Full document checking *)
  | Join
  | Finish
  (*******************************************************************)
  (* Non-supported commands, only for convenience.                   *)
  | ReadFile   of string
  | Tokenize   of string
  (*******************************************************************)
  (* Administrativia                                                 *)
  | Noop
  | Help
  | Quit
  (*******************************************************************)

let exec_cmd (cmd : cmd) =
  let doc = Stm.get_doc !doc_id in
  coq_protect @@ fun () -> match cmd with
  | NewDoc opts   ->
    let stm_options = Stm.AsyncOpts.default_opts in
    let require_libs = Option.default (["Coq.Init.Prelude", None, Some true]) opts.require_libs in
    let dft_ml, dft_vo =
      Serapi_paths.(coq_loadpath_default ~implicit:true ~coq_path:Coq_config.coqlib)
    in
    let ml_load_path = Option.default dft_ml opts.ml_load_path in
    let vo_load_path = Option.default dft_vo opts.vo_load_path in
    let ndoc = { Stm.doc_type = Stm.(Interactive opts.top_name)
               ; injections = List.map (fun x -> Stm.RequireInjection x) require_libs
               ; ml_load_path
               ; vo_load_path
               ; stm_options
               } in
    (* doc_id := fst Stm.(get_doc @@ new_doc ndoc); [] *)
    let _ = Stm.new_doc ndoc in
    doc_id := 0; []
  | Add (opt, s) ->
    let _doc, pa, res = ControlUtil.add_sentences ~doc opt s in
    QueryUtil.add_comments pa;
    res
  | Cancel st    -> List.concat @@ List.map (fun x -> snd @@ ControlUtil.(cancel_sentence ~doc x)) st
  | Exec st      -> ignore(Stm.observe ~doc st); []
  | Query (opt, qry)  -> [ObjList (exec_query opt qry)]
  | Print(opts, obj)  ->
    let st = Stm.state_of_id ~doc opts.sid in
    let sigma, env = context_of_st st in
    [ObjList [obj_print env sigma opts.pp obj]]
  | Parse(opt,s) ->
    Option.cata (fun ast -> [ObjList [CoqAst ast]]) []
      ControlUtil.(parse_sentence ~doc ~opt s)
  | Join              -> ignore(Stm.join ~doc); []
  | Finish            -> ignore(Stm.finish ~doc); []
  (*  *)
  | ReadFile f ->
    (
      let inc = open_in f in
      try
        let faddopts = { lim = None; ontop = None; newtip = None; verb = false; } in
        let fsize    = in_channel_length inc         in
        let fcontent = really_input_string inc fsize in
        let _doc, pa, res = ControlUtil.add_sentences ~doc faddopts fcontent in
        QueryUtil.add_comments pa;
        res
      with _ -> close_in inc; []
    )
  | Tokenize input ->
    let st = CLexer.Lexer.State.get () in
    begin try
        let istr = Stream.of_string input in
        let lex = CLexer.Lexer.tok_func istr in
        CLexer.Lexer.State.set st;
        let objs = Extra.stream_tok 0 [] lex in
        [ObjList [CoqTok objs]]
      with exn ->
        CLexer.Lexer.State.set st;
        raise exn
    end
  | Help           -> serproto_help (); []
  | Noop           -> []
  | Quit           -> []

type cmd_tag    = string
type tagged_cmd = cmd_tag * cmd

type feedback_content =
  | Processed
  | Incomplete
  | Complete
  | ProcessingIn of string
  | InProgress of int
  | WorkerStatus of string * string
  | AddedAxiom
  | FileDependency of string option * string
  | FileLoaded of string * string
  | Message of { level: Feedback.level ; loc : Loc.t option ; pp : Pp.t ; str: string }

type feedback =
  { doc_id   : Feedback.doc_id
  ; span_id  : Stateid.t
  ; route    : Feedback.route_id
  ; contents : feedback_content
  }

type answer =
  | Answer    of cmd_tag * answer_kind
  | Feedback  of feedback
