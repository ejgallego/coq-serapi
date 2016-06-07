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

let string_of_eosid esid =
  let open Feedback in
  match esid with
  | Edit  eid -> "eid: " ^ string_of_int eid
  | State sid -> "sid: " ^ (Stateid.to_string sid)

let string_of_feedback_content fb : string =
  let open Feedback in
  match fb with
  (* STM mandatory data (must be displayed) *)
    | Processed       -> "Processed."
    | Incomplete      -> "Incomplete."
    | Complete        -> "Complete."
    | ErrorMsg(_l, s) -> "ErrorMsg: " ^ s

  (* STM optional data *)
    | ProcessingIn s       -> "ProcessingIn: " ^ s
    | InProgress d         -> "InProgress: " ^ (string_of_int d)
    | WorkerStatus(w1, w2) -> "WorkerStatus: " ^ w1 ^ ", " ^ w2

  (* Generally useful metadata *)
    | Goals(_loc, g) -> "goals: " ^ g
    | AddedAxiom -> "AddedAxiom."
    | GlobRef (_loc, s1, s2, s3, s4) -> "GlobRef: " ^ s1 ^ ", " ^ s2 ^ ", " ^ s3 ^ ", " ^ s4
    | GlobDef (_loc, s1, s2, s3) -> "GlobDef: " ^ s1 ^ ", " ^ s2 ^ ", " ^ s3
    | FileDependency (os, s) -> "FileDep: " ^ (Option.default "" os) ^ ", " ^ s
    | FileLoaded (s1, s2)    -> "FileLoaded: " ^ s1 ^ " " ^ s2

    (* Extra metadata *)
    | Custom(_loc, msg, _xml) -> "Custom: " ^ msg
    (* Old generic messages *)
    | Message(_l, m) -> "Msg: " ^ Richpp.raw_print m

let pp_feedback fmt (fb : Feedback.feedback) =
  let open Feedback in
  Format.fprintf fmt "feedback for [%s]: %s"
    (string_of_eosid fb.id)
    (string_of_feedback_content fb.Feedback.contents)

