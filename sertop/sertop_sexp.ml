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

open Sexplib
open Sexplib.Conv

(* Optimize Pp.t inside feedback *)
let opt_answer ans =
  let open Serapi_protocol in
  match ans with
  | Feedback fb ->
    let open! Feedback in
    begin match fb with
      | { id; route; contents = Message (lvl, loc, msg) } ->
        if pp_opt_flag then
          Feedback {id; route; contents = Message(lvl, loc, coq_pp_opt msg) }
        else
          ans
      | _ ->
        ans
    end
  | _ ->
    ans

module SP = Serapi_protocol

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
      | CErrors.UserError(hdr,msg) ->
        let hdr = Option.default "" hdr in
        List [Atom "CErrors.UserError"; List [Atom hdr; sexp_of_std_ppcmds msg]]
      | _ -> assert false);
  Conv.Exn_converter.add [%extension_constructor CErrors.AlreadyDeclared] (function
      | CErrors.AlreadyDeclared msg ->
        List [Atom "CErrors.AlreadyDeclared"; List [sexp_of_std_ppcmds msg]]
      | _ -> assert false);
  Conv.Exn_converter.add [%extension_constructor Pretype_errors.PretypeError] (function
      (* Pretype Errors XXX what to do with _env, _envmap *)
      | Pretype_errors.PretypeError(_env, _evmap, pterr) ->
        List [Atom "Pretype_errors.PretypeError";
              List [Ser_pretype_errors.sexp_of_pretype_error pterr]]
      | _ -> assert false);
  Conv.Exn_converter.add [%extension_constructor ExplainErr.EvaluatedError] (function
      (* Cerrors *)
      | ExplainErr.EvaluatedError(msg, exn) -> begin
          match exn with
          | Some exn -> List [Atom "ExplainErr.EvaluatedError"; sexp_of_std_ppcmds msg; sexp_of_exn exn]
          | None     -> List [Atom "ExplainErr.EvaluatedError"; sexp_of_std_ppcmds msg]
        end
      | _ -> assert false);
  Conv.Exn_converter.add [%extension_constructor Proof_global.NoCurrentProof] (function
      | Proof_global.NoCurrentProof ->
        Atom "NoCurrentProof"
      | _ -> assert false)
(* Private... request Coq devs to make them public?
      | Errors.Anomaly(msgo, pp) ->
        Some (List [Atom "Anomaly"; sexp_of_option sexp_of_string msgo; sexp_of_std_ppcmds pp])
*)

module ST_Sexp = struct

module Loc      = Ser_loc
module Pp       = Ser_pp
module Names    = Ser_names
module Goptions = Ser_goptions
module Stateid  = Ser_stateid
module Context  = Ser_context
module Feedback = Ser_feedback
module Libnames = Ser_libnames
module Impargs  = Ser_impargs
module Constr     = Ser_constr
module Constrexpr = Ser_constrexpr
module Globnames  = Ser_globnames
module Proof      = Ser_proof
module Goal       = Ser_goal
(* Alias fails due to the [@@default in protocol] *)
(* module Stm        = Ser_stm *)
module Ser_stm    = Ser_stm

module Ltac_plugin = struct
  module Tacenv       = Ser_tacenv
  module Profile_ltac = Ser_profile_ltac
end

module Notation   = Ser_notation
module Xml_datatype = Ser_xml_datatype
module Notation_term = Ser_notation_term
module Vernacexpr   = Ser_vernacexpr
module Declarations = Ser_declarations
(* module Richpp       = Ser_richpp *)

module Serapi_goals = struct

  type 'a hyp =
    [%import: 'a Serapi_goals.hyp]
    [@@deriving sexp]

  type 'a reified_goal =
    [%import: 'a Serapi_goals.reified_goal]
    [@@deriving sexp]

end

(* Serialization to sexp *)
type coq_object =
  [%import: Serapi_protocol.coq_object]
  [@@deriving sexp]

exception AnswerExn of Sexp.t
let exn_of_sexp sexp = AnswerExn sexp

type print_format =
  [%import: Serapi_protocol.print_format]
  [@@deriving sexp]

type print_opt =
  [%import: Serapi_protocol.print_opt]
  [@@deriving sexp]

type query_pred =
  [%import: Serapi_protocol.query_pred]
  [@@deriving sexp]

type query_opt =
  [%import: Serapi_protocol.query_opt
  [@with
     Sexplib.Conv.sexp_list   := sexp_list;
     Sexplib.Conv.sexp_option := sexp_option;
  ]]
  [@@deriving sexp]

type query_cmd =
  [%import: Serapi_protocol.query_cmd]
  [@@deriving sexp]

type cmd_tag =
  [%import: Serapi_protocol.cmd_tag]
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

type answer_kind =
  [%import: Serapi_protocol.answer_kind
  [@with
     Stm.focus := Ser_stm.focus;
     Printexc.raw_backtrace := raw_backtrace;
  ]]
  [@@deriving sexp]

type answer =
  [%import: Serapi_protocol.answer]
  [@@deriving sexp]

let sexp_of_answer ans = sexp_of_answer (opt_answer ans)

type add_opts =
  [%import: Serapi_protocol.add_opts
  [@with
     Sexplib.Conv.sexp_option := sexp_option;
  ]]
  [@@deriving sexp]

type cmd =
  [%import: Serapi_protocol.cmd]
  [@@deriving sexp]

type tagged_cmd =
  [%import: Serapi_protocol.tagged_cmd]
  [@@deriving sexp]

end

(******************************************************************************)
(* Prelude Loading Hacks (to be improved)                                     *)
(******************************************************************************)

let ser_prelude_list coq_path =
  let mk_path prefix l = coq_path ^ "/" ^ prefix ^ "/" ^ String.concat "/" l in
  List.map (fun p -> ("Coq" :: p, mk_path "plugins"  p, true)) Sertop_prelude.coq_init_plugins  @
  List.map (fun p -> ("Coq" :: p, mk_path "theories" p, true)) Sertop_prelude.coq_init_theories

let ser_prelude_mod coq_path = [Sertop_prelude.coq_prelude_mod coq_path]

(******************************************************************************)
(* Global Protocol Options                                                    *)
(******************************************************************************)

type ser_printer =
  | SP_Sertop                   (* sertop custom printer (UTF-8, stronger quoting) *)
  | SP_Mach                     (* sexplib mach  printer *)
  | SP_Human                    (* sexplib human printer *)

type ser_opts = {
  (* Input output Options *)
  in_chan  : in_channel;        (* Input/Output channels                                *)
  out_chan : out_channel;
  printer  : ser_printer;       (* Printers                                             *)

  debug    : bool;
  print0   : bool;
  lheader  : bool;              (* Print lenght header (deprecated)                     *)

  (* Coq options *)
  coqlib   : string option;     (* Whether we should load the prelude, and its location *)
  implicit : bool;
  async    : Sertop_init.async_flags;
}

(******************************************************************************)
(* Input/Output                                                               *)
(******************************************************************************)
(*                                                                            *)
(* Until this point, we've been independent of a particular format or         *)
(* or serialization, with all the operations defined at the symbolic level.   *)
(*                                                                            *)
(* It is now time to unfortunately abandon our fairy-tale and face the real,  *)
(* ugly world in these last 40 lines!                                         *)
(*                                                                            *)
(******************************************************************************)

let is_cmd_quit cmd = match cmd with
  | SP.Quit -> true
  | _    -> false

(* XXX: Improve by using manual tag parsing. *)
let read_cmd cmd_id in_channel pp_error =
  let rec read_loop () =
    try
      let cmd_sexp = Sexp.input_sexp in_channel in
      begin
        try ST_Sexp.tagged_cmd_of_sexp cmd_sexp
        with
        | End_of_file   -> "EOF", SP.Quit
        | _exn ->
          (string_of_int cmd_id), ST_Sexp.cmd_of_sexp cmd_sexp
      end
    with
    | End_of_file   -> "EOF", SP.Quit
    | exn           -> pp_error (sexp_of_exn exn);
                       read_loop ()
  in read_loop ()

let out_sexp opts =
  let open Format                                                               in
  let pp_sexp = match opts.printer with
    | SP_Sertop -> Sertop_util.pp_sertop
    | SP_Mach   -> Sexp.pp
    | SP_Human  -> Sexp.pp_hum
  in

  let pp_term = if opts.print0 then fun fmt () -> fprintf fmt "%c" (Char.chr 0)
                               else fun fmt () -> fprintf fmt "@\n"             in
  if opts.lheader then
    fun fmt a ->
      fprintf str_formatter "@[%a@]%a%!" pp_sexp a pp_term ();
      let out = flush_str_formatter () in
      fprintf fmt "@[byte-length: %d@\n%s@]%!" (String.length out) out
  else
    fun fmt a -> fprintf fmt "@[%a@]%a%!" pp_sexp a pp_term ()

(** We could use Sexp.to_string too  *)
let out_answer opts =
  let pp_sexp = out_sexp opts in
  fun fmt a -> pp_sexp fmt (ST_Sexp.sexp_of_answer a)

let ser_loop ser_opts =

  let open List   in
  let open Format in

  (* XXX EG: I don't understand this well, why is this lock needed ??
     Review fork code in CoqworkmgrApi *)
  let pr_mutex     = Mutex.create ()                                   in
  let ser_lock f x = Mutex.lock   pr_mutex;
                     f x;
                     Mutex.unlock pr_mutex                             in
  let out_fmt      = formatter_of_out_channel ser_opts.out_chan        in
  let pp_answer    = ser_lock (out_answer ser_opts out_fmt)            in
  let pp_err       = ser_lock (out_sexp ser_opts out_fmt)              in
  let pp_ack cid   = pp_answer (SP.Answer (cid, SP.Ack))               in
  let pp_feed fb   = pp_answer (SP.Feedback fb)                        in


  (* Init Coq *)
  let _ = Sertop_init.coq_init {
    Sertop_init.fb_handler   = pp_feed;
    Sertop_init.aopts        = ser_opts.async;
    Sertop_init.iload_path   = Option.cata ser_prelude_list [] ser_opts.coqlib;
    Sertop_init.require_libs = Option.cata ser_prelude_mod  [] ser_opts.coqlib;
    Sertop_init.implicit_std = ser_opts.implicit;
    Sertop_init.top_name     = "SerTop";
    Sertop_init.ml_load      = None;
    Sertop_init.debug        = ser_opts.debug;
  } in

  (* Follow the same approach than coqtop for now: allow Coq to be
   * interrupted by Ctrl-C. Not entirely safe or race free... but we
   * trust the IDEs to send the signal on coherent IO state.
   *)
  Sys.catch_break true;

  (* Main loop *)
  let rec loop cmd_id =
    try
      let cmd_tag, cmd = read_cmd cmd_id ser_opts.in_chan pp_err          in
      pp_ack cmd_tag;
      iter pp_answer @@ map (fun a -> SP.Answer (cmd_tag, a)) (SP.exec_cmd cmd);
      if not (is_cmd_quit cmd) then loop (1+cmd_id)
    with Sys.Break -> loop (1+cmd_id)
  in loop 0

(* Registering of generic argument printers. These modules should be
   linked statically but we don't use ocamlbuild trickery *)
let _ =
  Ser_stdarg.register ();
  Ser_tacarg.register ();
  ()
