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
        Format.printf "@[Adding %d lines@]@\n%!" n_lines;
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

let create_from_file ~in_file ~async ~iload_path =

  let open Sertop_init in

  let stm_options =
    { enable_async = async;
      async_full   = false;
      deep_edits   = false;
    } in

  let ndoc = { Stm.doc_type = Stm.VoDoc in_file;
               require_libs = ["Coq.Init.Prelude", None, Some true];
               iload_path;
               stm_options  = Sertop_init.process_stm_flags stm_options;
               } in
  Stm.new_doc ndoc

let process_vernac ~mode ~pp ~doc ~st (CAst.{loc;v=vrn} as ast) =
  let open Format in
  let doc, n_st, tip = Stm.add ~doc ~ontop:st false ast in
  if tip <> `NewTip then
    (eprintf "Fatal Error, got no `NewTip`"; exit 1);
  let open Sertop_arg in
  let () = match mode with
    | C_parse -> ()
    | C_stats ->
      do_stats ?loc vrn
    | C_sexp ->
      printf "@[%a@]@\n%!" pp (Ser_vernacexpr.sexp_of_vernac_control vrn)
  in
  doc, n_st

let close_document ~mode =
  if mode = Sertop_arg.C_stats then
    Format.printf "Statistics:@\nSpecs:  %d@\nProofs: %d@\nMisc:   %d@\n%!"
      stats.specs stats.proofs stats.misc

(* Command line processing *)
let comp_version = Ser_version.ser_git_version

type compfun
  =  Sertop_arg.comp_mode
  -> bool
  -> Sertop_ser.ser_printer
  -> string option
  -> string
  -> Mltop.coq_path list
  -> Mltop.coq_path list
  -> Mltop.coq_path list
  -> string -> bool -> bool -> bool -> unit

open Cmdliner

let maincomp ~ext ~name ~desc ~(compfun:compfun) =
  let input_file =
    let doc = "Input " ^ ext ^ " file." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:("FILE"^ext) ~doc)
  in

  let comp_cmd =
    let doc = name ^ " Coq Compiler" in
    let man = [
      `S "DESCRIPTION";
      `P desc;
    ]
    in

    let open Sertop_arg in
    Term.(const compfun $ comp_mode $ debug $ printer $ async $ prelude $ ml_include_path $ load_path $ rload_path $ input_file $ omit_loc $ omit_att $ exn_on_opaque ),
    Term.info name ~version:comp_version ~doc ~man
  in

  try match Term.eval comp_cmd with
    | `Error _ -> exit 1
    | _        -> exit 0
  with any ->
    let (e, info) = CErrors.push any in
    Format.eprintf "Error: %a@\n%!" Pp.pp_with (CErrors.iprint (e, info));
    exit 1
