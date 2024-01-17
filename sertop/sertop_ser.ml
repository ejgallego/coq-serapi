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

open Sexplib
open Sexplib.Conv
open Serlib

type ser_printer =
  | SP_Sertop                   (* sertop custom printer (UTF-8, stronger quoting) *)
  | SP_Mach                     (* sexplib mach  printer *)
  | SP_Human                    (* sexplib human printer *)

let select_printer pr = match pr with
  | SP_Sertop -> Sertop_util.pp_sertop
  | SP_Mach   -> Sexp.pp
  | SP_Human  -> Sexp.pp_hum

module SP = Serapi.Serapi_protocol

(******************************************************************************)
(* Exception Registration                                                     *)
(******************************************************************************)

(* We play slow for now *)
let _ =
  (* XXX Finish this *)
  let open Sexp in
  let sexp_of_std_ppcmds pp = Atom (Pp.string_of_ppcmds pp) in
  Conv.Exn_converter.add [%extension_constructor SP.NoSuchState] (function
      (* Own things *)
      | SP.NoSuchState sid ->
        List [Atom "NoSuchState"; Ser_stateid.sexp_of_t sid]
      | _ -> assert false);
  Conv.Exn_converter.add [%extension_constructor CErrors.UserError] (function
      (* Errors *)
      | CErrors.UserError(msg) ->
        List [Atom "CErrors.UserError"; List [sexp_of_std_ppcmds msg]]
      | _ -> assert false);
  Conv.Exn_converter.add [%extension_constructor DeclareUniv.AlreadyDeclared] (function
      | DeclareUniv.AlreadyDeclared (msg, id) ->
        List [Atom "Declare.AlreadyDeclared"; List [sexp_of_option sexp_of_string msg; Ser_names.Id.sexp_of_t id]]
      | _ -> assert false);
  Conv.Exn_converter.add [%extension_constructor Pretype_errors.PretypeError] (function
      (* Pretype Errors XXX what to do with _env, _envmap *)
      | Pretype_errors.PretypeError(_env, _evmap, pterr) ->
        List [Atom "Pretype_errors.PretypeError";
              List [Ser_pretype_errors.sexp_of_pretype_error pterr]]
      | _ -> assert false);
  (* Conv.Exn_converter.add [%extension_constructor Proof_global.NoCurrentProof] (function
   *     | Proof_global.NoCurrentProof ->
   *       Atom "NoCurrentProof"
   *     | _ -> assert false) *)
(* Private... request Coq devs to make them public?
      | Errors.Anomaly(msgo, pp) ->
        Some (List [Atom "Anomaly"; sexp_of_option sexp_of_string msgo; sexp_of_std_ppcmds pp])
*)

(******************************************************************************)
(* Serialization of the Protocol                                              *)
(******************************************************************************)

module Loc      = Ser_loc
module CAst     = Ser_cAst
module Pp       = Ser_pp
module Names    = Ser_names
module Environ  = Ser_environ
module Goptions = Ser_goptions
module Coqargs  = Ser_coqargs
module Stateid  = Ser_stateid
module Evar     = Ser_evar
module Context  = Ser_context
module Feedback = Ser_feedback
module Libnames = Ser_libnames
module Lib      = Ser_lib
module Nametab    = Ser_nametab
module Globnames  = Ser_globnames
module Impargs    = Ser_impargs
module Constr     = Ser_constr
module EConstr    = Ser_eConstr
module Constrexpr = Ser_constrexpr
module Proof      = Ser_proof
module Tok        = Ser_tok
module Ppextend   = Ser_ppextend
module Notation_gram = Ser_notation_gram
module Genarg     = Ser_genarg
module Loadpath   = Ser_loadpath
module Printer    = Ser_printer

(* Alias fails due to the [@@default in protocol] *)
(* module Stm        = Ser_stm *)
module Ser_stm    = Ser_stm

module LtacX_common_plugin = struct
  module Profile_ltac = Serlib_ltacX_common.Ser_profile_ltac
end

module Ltac_plugin = struct
  module Tacenv       = Serlib_ltac.Ser_tacenv
  module Tacexpr      = Serlib_ltac.Ser_tacexpr
end

module Notation   = Ser_notation
module Xml_datatype = Ser_xml_datatype
module Notation_term = Ser_notation_term
module Vernacexpr   = Ser_vernacexpr
module Declarations = Ser_declarations
(* module Richpp       = Ser_richpp *)

module Summary = Ser_summary

module Serapi = struct
module Serapi_goals = struct

  type 'a hyp =
    [%import: 'a Serapi.Serapi_goals.hyp]
    [@@deriving sexp]

  type info =
    [%import: Serapi.Serapi_goals.info]
    [@@deriving sexp]

  type 'a reified_goal =
    [%import: 'a Serapi.Serapi_goals.reified_goal]
    [@@deriving sexp]

  type 'a ser_goals =
    [%import: 'a Serapi.Serapi_goals.ser_goals]
    [@@deriving sexp]

end

module Serapi_assumptions = struct
type ax_ctx =
  [%import: Serapi.Serapi_assumptions.ax_ctx]
  [@@deriving sexp]

type t =
  [%import: Serapi.Serapi_assumptions.t]
  [@@deriving sexp]

end

module Serapi_protocol = Serapi.Serapi_protocol

end

(* Serialization to sexp *)
type coq_object =
  [%import: Serapi.Serapi_protocol.coq_object]
  [@@deriving sexp]

exception AnswerExn of Sexp.t
let exn_of_sexp sexp = AnswerExn sexp

type print_format =
  [%import: Serapi.Serapi_protocol.print_format]
  [@@deriving sexp]

type format_opt =
  [%import: Serapi.Serapi_protocol.format_opt]
  [@@deriving sexp]

type print_opt =
  [%import: Serapi.Serapi_protocol.print_opt]
  [@@deriving sexp]

type query_pred =
  [%import: Serapi.Serapi_protocol.query_pred]
  [@@deriving sexp]

type query_opt =
  [%import: Serapi.Serapi_protocol.query_opt
  [@with
     Sexplib.Conv.sexp_list   := sexp_list;
     Sexplib.Conv.sexp_option := sexp_option;
  ]]
  [@@deriving sexp]

type query_cmd =
  [%import: Serapi.Serapi_protocol.query_cmd]
  [@@deriving sexp]

type cmd_tag =
  [%import: Serapi.Serapi_protocol.cmd_tag]
  [@@deriving sexp]

type location =
  [%import: Printexc.location]
  [@@deriving sexp]

type raw_backtrace = Printexc.raw_backtrace
let raw_backtrace_of_sexp _ = Printexc.get_raw_backtrace ()

type slot_rep = {
  slot_loc : location option;
  slot_idx : int;
  slot_str : string option;
} [@@deriving sexp]

let to_slot_rep idx bs = {
  slot_loc = Printexc.Slot.location bs;
  slot_idx = idx;
  slot_str = Printexc.Slot.format idx bs;
}

let sexp_of_backtrace_slot idx bs =
  sexp_of_slot_rep (to_slot_rep idx bs)

let sexp_of_raw_backtrace (bt : Printexc.raw_backtrace) : Sexp.t =
  let bt = Printexc.backtrace_slots bt in
  let bt = Option.map Array.(mapi sexp_of_backtrace_slot) bt in
  let bt = sexp_of_option (sexp_of_array (fun x -> x)) bt in
  Sexp.(List [Atom "Backtrace"; bt])

module ExnInfo = struct
  type t =
    [%import: Serapi.Serapi_protocol.ExnInfo.t
    [@with
       Stm.focus := Ser_stm.focus;
       Printexc.raw_backtrace := raw_backtrace;
       Stdlib.Printexc.raw_backtrace := raw_backtrace;
    ]]
    [@@deriving sexp]
end

type answer_kind =
  [%import: Serapi.Serapi_protocol.answer_kind
  [@with
    Exninfo.t := Exninfo.t;
    Stm.add_focus := Ser_stm.add_focus;
  ]]
  [@@deriving sexp]

type feedback_content =
  [%import: Serapi.Serapi_protocol.feedback_content]
  [@@deriving sexp]

type feedback =
  [%import: Serapi.Serapi_protocol.feedback]
  [@@deriving sexp]

type answer =
  [%import: Serapi.Serapi_protocol.answer]
  [@@deriving sexp]

type add_opts =
  [%import: Serapi.Serapi_protocol.add_opts
  [@with
     Sexplib.Conv.sexp_option := sexp_option;
  ]]
  [@@deriving sexp]

type newdoc_opts =
  [%import: Serapi.Serapi_protocol.newdoc_opts
  [@with
     (* Stm.interactive_top      := Ser_stm.interactive_top; *)
     Sexplib.Conv.sexp_list   := sexp_list;
     Sexplib.Conv.sexp_option := sexp_option;
  ]]
  [@@deriving sexp]

type save_opts =
  [%import: Serapi.Serapi_protocol.save_opts]
  [@@deriving sexp]

type parse_entry =
  [%import: Serapi.Serapi_protocol.parse_entry]
  [@@deriving sexp]

type parse_opt =
  [%import: Serapi.Serapi_protocol.parse_opt
  [@with
     Sexplib.Conv.sexp_option := sexp_option;
  ]]
  [@@deriving sexp]

type cmd =
  [%import: Serapi.Serapi_protocol.cmd]
  [@@deriving sexp]

type tagged_cmd =
  [%import: Serapi.Serapi_protocol.tagged_cmd]
  [@@deriving sexp]

type sentence = Sentence of Tok.t CAst.t list
  [@@deriving sexp]
