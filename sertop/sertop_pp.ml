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

open Format

(** This module includes all of sertop custom Format-based printers
    for Coq datatypes *)

type 'a pp = formatter -> 'a -> unit

(************************************************************************)
(* Print Helpers                                                        *)
(************************************************************************)

let pp_str fmt str = fprintf fmt "%s" str

let pp_opt pp fmt opt = match opt with
  | None   -> ()
  | Some x -> fprintf fmt "%a" pp x

let rec pp_list ?sep pp fmt l = match l with
    []         -> fprintf fmt ""
  | csx :: []  -> fprintf fmt "@[%a@]" pp csx
  | csx :: csl -> fprintf fmt "@[%a@]%a@;%a" pp csx (pp_opt pp_str) sep (pp_list ?sep pp) csl

(************************************************************************)
(* Statid                                                               *)
(************************************************************************)
let pp_stateid fmt id = fprintf fmt "%d" (Stateid.to_int id)

let string_of_eosid esid =
  let open Feedback in
  match esid with
  | Edit  eid -> "eid: " ^ string_of_int eid
  | State sid -> "sid: " ^ (Stateid.to_string sid)

(************************************************************************)
(* Feedback                                                             *)
(************************************************************************)
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

(************************************************************************)
(* Xml                                                                  *)
(************************************************************************)
let pp_attr fmt (xtag, att) =
  Format.fprintf fmt "%s = %s" xtag att

let rec pp_xml fmt (xml : Xml_datatype.xml) = match xml with
  | Xml_datatype.Element (tag, att, more) ->
    Format.fprintf fmt "@[<%s @[%a@]>@,%a@,</%s>@]" tag (pp_list pp_attr) att (pp_list pp_xml) more tag
  | Xml_datatype.PCData str -> Format.fprintf fmt "%s" str

