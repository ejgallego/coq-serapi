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

open Ser_loc
open Ser_names
open Ser_goptions
open Ser_stateid
open Ser_richpp
open Ser_feedback
open Ser_libnames
open Ser_impargs
open Ser_constr
open Ser_constrexpr
open Ser_globnames
open Ser_proof
open Ser_stm
open Ser_tacenv
open Ser_profile_ltac

module SP = Serapi_protocol

(******************************************************************************)
(* Exception Registration                                                     *)
(******************************************************************************)

(* We play slow for now *)
let _ =
  (* XXX Finish this *)
  let open Sexp in
  let sexp_of_std_ppcmds pp = Atom (Pp.string_of_ppcmds pp) in
  Conv.Exn_converter.add_slow (function
      (* Own things *)
      | SP.NoSuchState sid ->
        Some (List [Atom "NoSuchState"; sexp_of_stateid sid])
      (* Errors *)
      | CErrors.UserError(e,msg) ->
        Some (List [Atom "Errors.UserError"; List [Atom e; sexp_of_std_ppcmds msg]])
      | CErrors.AlreadyDeclared msg ->
        Some (List [Atom "Errors.AlreadyDeclared"; List [sexp_of_std_ppcmds msg]])
      (* Pretype Errors XXX what to do with _env, _envmap *)
      | Pretype_errors.PretypeError(_env, _evmap, pterr) ->
        Some (List [Atom "Pretype_errors.PretypeError";
                    List [Ser_pretype_errors.sexp_of_pretype_error pterr]])
      (* Cerrors *)
      | ExplainErr.EvaluatedError(msg, exn) -> Some (
          match exn with
          | Some exn -> List [Atom "Cerrors.EvaluatedError"; sexp_of_std_ppcmds msg; sexp_of_exn exn]
          | None     -> List [Atom "Cerrors.EvaluatedError"; sexp_of_std_ppcmds msg]
        )
      | Proof_global.NoCurrentProof ->
        Some (Atom "NoCurrentProof")
(* Private... request Coq devs to make them public?
      | Errors.Anomaly(msgo, pp) ->
        Some (List [Atom "Anomaly"; sexp_of_option sexp_of_string msgo; sexp_of_std_ppcmds pp])
*)
      | _ -> None

    )

(* Serialization to sexp *)
type coq_object =
  [%import: Serapi_protocol.coq_object
  [@with
     Constr.constr                 := constr;
     Constrexpr.constr_expr        := constr_expr;
     Globnames.global_reference    := global_reference;
     Goptions.option_name          := option_name;
     Goptions.option_state         := option_state;
     Impargs.implicits_list        := implicits_list;
     Libnames.qualid               := qualid;
     Loc.t                         := loc;
     Names.Id.t                    := id;
     Names.KerName.t               := kername;
     Profile_ltac.ltacprof_results := ltacprof_results;
     Proof.pre_goals               := pre_goals;
     Richpp.richpp                 := richpp;
     Tacenv.ltac_entry             := ltac_entry;
  ]]
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
  [%import: Serapi_protocol.query_pred
  [@with
     Stateid.t := stateid;
  ]]
  [@@deriving sexp]

type query_opt =
  [%import: Serapi_protocol.query_opt
  [@with
     Stateid.t                := stateid;
     Sexplib.Conv.sexp_list   := sexp_list;
     Sexplib.Conv.sexp_option := sexp_option;
     Feedback.route_id        := route_id;
  ]]
  [@@deriving sexp]

type query_cmd =
  [%import: Serapi_protocol.query_cmd
  [@with
     Stateid.t := stateid;
  ]]
  [@@deriving sexp]

type cmd_tag =
  [%import: Serapi_protocol.cmd_tag]
  [@@deriving sexp]

type answer_kind =
  [%import: Serapi_protocol.answer_kind
  [@with
     Loc.t                         := loc;
     Stateid.t := stateid;
     Stm.focus := focus;
  ]]
  [@@deriving sexp]

type answer =
  [%import: Serapi_protocol.answer
  [@with
     Feedback.feedback := feedback;
  ]]
  [@@deriving sexp]

type add_opts =
  [%import: Serapi_protocol.add_opts
  [@with
     Stateid.t := stateid;
     Sexplib.Conv.sexp_option := sexp_option;
  ]]
  [@@deriving sexp]

type control_cmd =
  [%import: Serapi_protocol.control_cmd
  [@with
     Goptions.option_name          := option_name;
     Goptions.option_state         := option_state;
     Goptions.option_value         := option_value;
     Stateid.t                     := stateid;
  ]]
  [@@deriving sexp]

type cmd =
  [%import: Serapi_protocol.cmd]
  [@@deriving sexp]

type tagged_cmd =
  [%import: Serapi_protocol.tagged_cmd]
  [@@deriving sexp]

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

type ser_opts = {
  coqlib   : string option;       (* Whether we should load the prelude, and its location *)
  in_chan  : in_channel;          (* Input/Output channels                                *)
  out_chan : out_channel;
  human    : bool;                (* Output function to use                               *)
  print0   : bool;
  lheader  : bool;
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
  | Control Quit -> true
  | _            -> false

(* XXX: Improve by using manual tag parsing. *)
let read_cmd cmd_id in_channel pp_error =
  let rec read_loop () =
    try
      let cmd_sexp = Sexp.input_sexp in_channel in
      begin
        try tagged_cmd_of_sexp cmd_sexp
        with
        | End_of_file   -> "EOF", Control Quit
        | _exn ->
          (string_of_int cmd_id), cmd_of_sexp cmd_sexp
      end
    with
    | End_of_file   -> "EOF", Control Quit
    | exn           -> pp_error (sexp_of_exn exn);
                       read_loop ()
  in read_loop ()

let out_sexp opts =
  let open Format                                                               in
  let pp_sexp = if opts.human  then Sexp.pp_hum
                               else Sexp.pp                                     in

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
  fun fmt a -> pp_sexp fmt (sexp_of_answer a)

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
  let pp_ack cid   = pp_answer (Answer (cid, Ack))                     in
  let pp_feed fb   = pp_answer (Feedback fb)                           in

  (* Init Coq *)
  Sertop_init.coq_init {
    Sertop_init.fb_handler   = pp_feed;
    Sertop_init.aopts        = ser_opts.async;
    Sertop_init.iload_path   = Option.cata ser_prelude_list [] ser_opts.coqlib;
    Sertop_init.require_libs = Option.cata ser_prelude_mod  [] ser_opts.coqlib;
    Sertop_init.implicit_prelude = ser_opts.implicit;
  };

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
      iter pp_answer @@ map (fun a -> Answer (cmd_tag, a)) (SP.exec_cmd cmd);
      if not (is_cmd_quit cmd) then loop (1+cmd_id)
    with Sys.Break -> loop (1+cmd_id)
  in loop 0

