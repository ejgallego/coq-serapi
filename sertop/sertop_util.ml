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

let rec coq_pp_opt (d : Pp.t) = let open Pp in
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
      | Ppcmd_glue [x]  -> repr (coq_pp_opt x)
      | Ppcmd_glue l    -> Ppcmd_glue List.(map coq_pp_opt (map unrepr (flatten_glue (map repr l))))
      | Ppcmd_box(bt,d) -> Ppcmd_box(bt, coq_pp_opt d)
      | Ppcmd_tag(t, d) -> Ppcmd_tag(t,  coq_pp_opt d)
      | d -> d
    )

(* Adjust positions from byte to UTF-8 chars *)
(* XXX: Move to serapi/ *)
(* We only do adjustement for messages for now. *)
module F = Feedback

let feedback_content_pos_filter txt (fbc : F.feedback_content) : F.feedback_content =
  let adjust _txt loc = loc in
  match (fbc : F.feedback_content) with
  | F.Message (lvl,loc,msg) -> F.Message (lvl, adjust txt loc, msg)
  | _                       -> fbc

let feedback_pos_filter text (fb : F.feedback) : F.feedback =
  { fb with F.contents = feedback_content_pos_filter text fb.F.contents; }


(* Optimizes and filters feedback *)
type fb_filter_opts = {
  pp_opt : bool;
}

let default_fb_filter_opts = {
  pp_opt = true;
}

let feedback_content_tr (fb : F.feedback_content) : Serapi.Serapi_protocol.feedback_content =
  match fb with
  | F.Message (level, loc, pp) ->
    let str = Pp.string_of_ppcmds pp in
    Message { level; loc; pp; str }
  | F.Processed -> Processed
  | F.Incomplete -> Incomplete
  | F.Complete -> Complete
  | F.ProcessingIn s -> ProcessingIn s
  | F.InProgress i -> InProgress i
  | F.WorkerStatus (s1,s2) -> WorkerStatus (s1,s2)
  | F.AddedAxiom -> AddedAxiom
  | F.GlobRef (_, _, _, _, _) -> assert false
  | F.GlobDef (_, _, _, _) -> assert false
  | F.FileDependency (o, p) -> FileDependency (o,p)
  | F.FileLoaded (o, p) -> FileLoaded (o, p)
  | F.Custom (_, _, _) -> assert false

let feedback_tr (fb : Feedback.feedback) : Serapi.Serapi_protocol.feedback =
  match fb with
  | { doc_id; span_id; route; contents } ->
    let contents = feedback_content_tr contents in
    { doc_id; span_id; route; contents }

let feedback_opt_filter ?(opts=default_fb_filter_opts) =
  let open Feedback in function
    | { F.contents = Message (lvl, loc, msg); _ } as fb ->
      Some (if opts.pp_opt
            then { fb with contents = Message(lvl, loc, coq_pp_opt msg) }
            else fb)
    | { F.contents = FileDependency _ ; _ } -> None
    | fb -> Some fb
