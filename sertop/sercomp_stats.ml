(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

type stats =
  { mutable specs  : int
  ; mutable proofs : int
  ; mutable misc   : int
  }

let stats =
  { specs  = 0
  ; proofs = 0
  ; misc   = 0
  }

(* XXX: Move to sertop_stats.ml *)
let do_stats =
  let proof_loc = ref None in
  fun CAst.{ loc ; v = { Vernacexpr.expr; _ } } ->
  let open Vernacexpr in
  let incS ?loc f =
    Option.cata (fun loc ->
        let n_lines = Loc.(loc.line_nb_last - loc.line_nb + 1) in
        Format.printf "@[Adding %d lines@]@\n%!" n_lines;
        f + n_lines) f loc
  in
  match expr with
  (* Definition *)
  | VernacSynPure (VernacDefinition (_,_,_)
  | VernacFixpoint   (_,_)
  | VernacInductive  (_,_)
  | VernacCoFixpoint (_,_))
  | VernacSynterp (VernacNotation (_,_)) ->
    stats.specs <- incS ?loc stats.specs

  (* Proofs *)
  | VernacSynPure (VernacStartTheoremProof (_,_)) ->
    stats.specs <- incS ?loc stats.specs;
    Option.iter (fun loc -> proof_loc := Some Loc.(loc.line_nb_last)) loc

  | VernacSynPure (VernacProof (_,_)) -> ()
  (* XXX: Should we use the +1 rule here, what happens for proofs:
     Proof. exact: L. Qed.
   *)
  | VernacSynPure (VernacEndProof _) -> Option.iter (fun ll -> Option.iter (fun loc ->
                                         stats.proofs <- stats.proofs + (Loc.(loc.line_nb) - ll) + 1
                                       ) loc ) !proof_loc;
                                       proof_loc := None
  (* This is tricky.. *)
  (* This is Ltac := ... *)
  | VernacSynterp (VernacExtend ({ Vernacexpr.ext_entry = "VernacDeclareTacticDefinition"; _ },_))
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

let print_stats () =
  Format.printf "Statistics:@\nSpecs:  %d@\nProofs: %d@\nMisc:   %d@\n%!"
    stats.specs stats.proofs stats.misc
