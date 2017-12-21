(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin, batch compiler                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

open Ser_vernacexpr

type stats = {
  mutable specs  : int;
  mutable proofs : int;
  mutable misc   : int;
}

let stats = {
  specs  = 0;
  proofs = 0;
  misc   = 0;
}

(* XXX: Move to sertop_stats.ml *)
let do_stats =
  let proof_loc = ref None in
  fun ?loc (vrn : Vernacexpr.vernac_control) ->
  let open Vernacexpr in
  let incS ?loc f =
    Option.cata (fun loc ->
        let n_lines = Loc.(loc.line_nb_last - loc.line_nb + 1) in
        Format.eprintf "Adding %d lines @\n%!" n_lines;
        f + n_lines) f loc
  in
  match Vernacprop.under_control vrn with
  (* Definition *)
  | VernacDefinition (_,_,_)
  | VernacFixpoint   (_,_)
  | VernacInductive  (_,_,_,_)
  | VernacCoFixpoint (_,_)
  | VernacNotation   (_,_,_) ->
    stats.specs <- incS ?loc stats.specs

  (* Proofs *)
  | VernacStartTheoremProof (_,_) ->
    stats.specs <- incS ?loc stats.specs;
    Option.iter (fun loc -> proof_loc := Some Loc.(loc.line_nb_last)) loc

  | VernacProof (_,_)               -> ()
  (* XXX: Should we use the +1 rule here, what happens for proofs:
     Proof. exact: L. Qed.
   *)
  | VernacEndProof _                -> Option.iter (fun ll -> Option.iter (fun loc ->
                                         stats.proofs <- stats.proofs + (Loc.(loc.line_nb) - ll) + 1
                                       ) loc ) !proof_loc;
                                       proof_loc := None
  (* This is tricky.. *)
  (* This is Ltac := ... *)
  | VernacExtend (("VernacDeclareTacticDefinition",_),_)
                                    -> stats.proofs <- incS ?loc stats.proofs;

  | _                               -> if Option.is_empty !proof_loc then stats.misc <- incS ?loc stats.misc

(*
  match vrn with
  | VernacLoad (_,_) -> (??)
  | VernacTime _ -> (??)
  | VernacRedirect (_,_) -> (??)
  | VernacTimeout (_,_) -> (??)
  | VernacFail _ -> (??)
  | VernacError _ -> (??)
  | VernacSyntaxExtension (_,_) -> (??)
  | VernacOpenCloseScope (_,_) -> (??)
  | VernacDelimiters (_,_) -> (??)
  | VernacBindScope (_,_) -> (??)
  | VernacInfix (_,_,_,_) -> (??)
  | VernacNotationAddFormat (_,_,_) -> (??)
  | VernacStartTheoremProof (_,_,_) -> (??)
  | VernacExactProof _ -> (??)
  | VernacAssumption (_,_,_) -> (??)
  | VernacScheme _ -> (??)
  | VernacCombinedScheme (_,_) -> (??)
  | VernacUniverse _ -> (??)
  | VernacConstraint _ -> (??)
  | VernacBeginSection _ -> (??)
  | VernacEndSegment _ -> (??)
  | VernacRequire (_,_,_) -> (??)
  | VernacImport (_,_) -> (??)
  | VernacCanonical _ -> (??)
  | VernacCoercion (_,_,_,_) -> (??)
  | VernacIdentityCoercion (_,_,_,_) -> (??)
  | VernacNameSectionHypSet (_,_) -> (??)
  | VernacInstance (_,_,_,_,_) -> (??)
  | VernacContext _ -> (??)
  | VernacDeclareInstances (_,_) -> (??)
  | VernacDeclareClass _ -> (??)
  | VernacDeclareModule (_,_,_,_) -> (??)
  | VernacDefineModule (_,_,_,_,_) -> (??)
  | VernacDeclareModuleType (_,_,_,_) -> (??)
  | VernacInclude _ -> (??)
  | VernacSolveExistential (_,_) -> (??)
  | VernacAddLoadPath (_,_,_) -> (??)
  | VernacRemoveLoadPath _ -> (??)
  | VernacAddMLPath (_,_) -> (??)
  | VernacDeclareMLModule _ -> (??)
  | VernacChdir _ -> (??)
  | VernacWriteState _ -> (??)
  | VernacRestoreState _ -> (??)
  | VernacResetName _ -> (??)
  | VernacResetInitial  -> (??)
  | VernacBack _ -> (??)
  | VernacBackTo _ -> (??)
  | VernacCreateHintDb (_,_) -> (??)
  | VernacRemoveHints (_,_) -> (??)
  | VernacHints (_,_,_) -> (??)
  | VernacSyntacticDefinition (_,_,_,_) -> (??)
  | VernacDeclareImplicits (_,_) -> (??)
  | VernacArguments (_,_,_,_) -> (??)
  | VernacArgumentsScope (_,_) -> (??)
  | VernacReserve _ -> (??)
  | VernacGeneralizable _ -> (??)
  | VernacSetOpacity _ -> (??)
  | VernacSetStrategy _ -> (??)
  | VernacUnsetOption _ -> (??)
  | VernacSetOption (_,_) -> (??)
  | VernacAddOption (_,_) -> (??)
  | VernacRemoveOption (_,_) -> (??)
  | VernacMemOption (_,_) -> (??)
  | VernacPrintOption _ -> (??)
  | VernacCheckMayEval (_,_,_) -> (??)
  | VernacGlobalCheck _ -> (??)
  | VernacDeclareReduction (_,_) -> (??)
  | VernacPrint _ -> (??)
  | VernacSearch (_,_,_) -> (??)
  | VernacLocate _ -> (??)
  | VernacRegister (_,_) -> (??)
  | VernacComments _ -> (??)
  | VernacStm _ -> (??)
  | VernacAbort _ -> (??)
  | VernacAbortAll  -> (??)
  | VernacRestart  -> (??)
  | VernacUndo _ -> (??)
  | VernacUndoTo _ -> (??)
  | VernacBacktrack (_,_,_) -> (??)
  | VernacFocus _ -> (??)
  | VernacUnfocus  -> (??)
  | VernacUnfocused  -> (??)
  | VernacBullet _ -> (??)
  | VernacProgram _ -> (??)
  | VernacSubproof _ -> (??)
  | VernacEndSubproof  -> (??)
  | VernacShow _ -> (??)
  | VernacCheckGuard  -> (??)
  | VernacProofMode _ -> (??)
  | VernacToplevelControl _ -> (??)
  | VernacExtend (_,_) -> (??)
  | VernacPolymorphic (_,_) -> (??)
  | VernacLocal (_,_) -> (??)
*)

let process_vernac pp ~doc st (loc, vrn) =
  let open Format in
  let doc, n_st, tip = Stm.add ~doc ~ontop:st false (loc, vrn) in
  if tip <> `NewTip then
    (eprintf "Fatal Error, got no `NewTip`"; exit 1);
  do_stats ?loc vrn;
  printf "@[%a@]@\n @[%a@]@\n%!" Pp.pp_with (Pp.pr_opt Topfmt.pr_loc loc)
                                 pp (sexp_of_vernac_control vrn);
  doc, n_st

let parse_document pp ~doc sid in_pa =
  let stt = ref (doc, sid) in
  try while true do
      let east = Stm.parse_sentence ~doc:(fst !stt) (snd !stt) in_pa in
      stt := process_vernac pp ~doc:(fst !stt) (snd !stt) east
    done
  with any ->
    let (e, _info) = CErrors.push any in
    match e with
    | Stm.End_of_input -> ()
    | any          ->
      let (e, info) = CErrors.push any in
      Format.eprintf "%a@\n%!" Pp.pp_with (CErrors.iprint (e, info))

 (* Format.eprintf "Error in parsing@\n%!" (\* XXX: add loc *\) *)

let close_document () =
  let open Format in
  printf "Statistics:@\nSpecs:  %d@\nProofs: %d@\nMisc:   %d@\n%!" stats.specs stats.proofs stats.misc

let sercomp printer coq_path in_file =
  let open Sertop_init in
  let pp_sexp = match printer with
    | Sertop_sexp.SP_Sertop -> Sertop_util.pp_sertop
    | Sertop_sexp.SP_Mach   -> Sexp.pp
    | Sertop_sexp.SP_Human  -> Sexp.pp_hum
  in
  let in_chan = open_in in_file            in
  let in_strm = Stream.of_channel in_chan  in

  let in_pa   = Pcoq.Gram.parsable ~file:(Loc.InFile in_file) in_strm in
  let sload_path = coq_loadpath_default ~implicit:true ~coq_path in

  let doc,sid = coq_init {
    fb_handler   = (fun _ -> ());
    aopts        = { enable_async = None;
                     async_full   = false;
                     deep_edits   = false;
                   };
    iload_path   = sload_path;
    require_libs = ["Coq.Init.Prelude", None, Some true];
    top_name     = "SerComp";
    ml_load      = None;
    debug        = false;
  } in

  parse_document pp_sexp ~doc sid in_pa;
  close_in in_chan;
  close_document ()

(* Command line processing *)
let sercomp_version = Ser_version.ser_git_version

open Cmdliner

let input_file =
  let doc = "Input .v file." in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FILE.v" ~doc)

let sertop_cmd =
  let doc = "SerComp Coq Compiler" in
  let man = [
    `S "DESCRIPTION";
    `P "Experimental Coq Compiler with serialization support. Currently it just prints some stats on the file."
  ]
  in
  let open Sercmdopt in
  Term.(const sercomp $ printer $ prelude $ input_file),
  Term.info "sercomp" ~version:sercomp_version ~doc ~man

let main () =
  try match Term.eval sertop_cmd with
    | `Error _ -> exit 1
    | _        -> exit 0
  with any ->
    let (e, info) = CErrors.push any in
    Format.eprintf "%a@\n%!" Pp.pp_with (CErrors.iprint (e, info));
    exit 1

let _ = main ()
