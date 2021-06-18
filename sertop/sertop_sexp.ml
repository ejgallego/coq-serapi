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

module SP = Serapi.Serapi_protocol

(******************************************************************************)
(* Global Protocol Options                                                    *)
(******************************************************************************)

type ser_opts =
{ in_chan  : in_channel          (* Input/Output channels                      *)
; out_chan : out_channel
                                 (* Printers                                   *)
; printer  : Sertop_ser.ser_printer

; debug    : bool
; allow_sprop : bool
; indices_matter : bool
; print0   : bool
; lheader  : bool                (* Print lenght header (deprecated)           *)

  (* Coq options *)
; no_init  : bool                (* Whether to create the initial document     *)
; no_prelude : bool              (* Whether to load stdlib's prelude           *)
; topfile  : string option       (* Top name is derived from topfile name      *)
; ml_path : string list
; vo_path : Loadpath.vo_path list (** From -R and -Q options usually           *)
; async    : Sertop_init.async_flags
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

type sertop_cmd =
  | SerApi of Sertop_ser.tagged_cmd
  (** Regular   *)
  | Fork of { fifo_in : string; fifo_out : string }
  (** Fork SerAPI to a new process, useful for people doing search
     [but heavy], the forked process will create and use the provided
     FIFO's for input / output *)
  | Quit
  (** Exit sertop *)
  [@@deriving sexp]

let is_cmd_quit cmd = match cmd with
  | Quit -> true
  | _    -> false

(* Loop state *)
module Ctx = struct

  type t =
    { in_chan : Stdlib.in_channel
    ; out_chan : Stdlib.out_channel
    ; out_fmt : Format.formatter
    ; cmd_id : int
    ; st : SP.State.t
    }

  let make ?in_file ?ldir ~cmd_id ~in_chan ~out_chan () =
    let out_fmt = Format.formatter_of_out_channel out_chan in
    let st = SP.State.make ?in_file ?ldir () in
    { out_chan; out_fmt; in_chan; cmd_id; st }

end

(* XXX: Improve by using manual tag parsing. *)
let read_cmd ~(ctx : Ctx.t) ~pp_err =
  let rec read_loop () =
    try
      let cmd_sexp = Sexp.input_sexp ctx.in_chan in
      begin
        try sertop_cmd_of_sexp cmd_sexp
        with
        | _exn ->
          begin
            try SerApi (Sertop_ser.tagged_cmd_of_sexp cmd_sexp)
            with
            | _exn ->
              SerApi (string_of_int ctx.cmd_id, Sertop_ser.cmd_of_sexp cmd_sexp)
          end
      end
    with
    | End_of_file   ->
      Quit
    | exn           ->
      pp_err ctx.out_fmt (sexp_of_exn exn);
      (read_loop [@ocaml.tailcall]) ()
  in read_loop ()

let out_sexp opts =
  let open Format                                                               in

  let pp_sexp = Sertop_ser.select_printer opts.printer in

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
  fun fmt a -> pp_sexp fmt (Sertop_ser.sexp_of_answer a)

(** Set the topname from optional topfile string or default if None **)
let doc_type topfile =
  match topfile with
  | None ->
    let sertop_dp = Names.(DirPath.make [Id.of_string "SerTop"]) in
    Stm.Interactive (TopLogical sertop_dp)
  | Some filename -> Stm.Interactive (Coqargs.TopPhysical filename)

let process_serloop_cmd ~(ctx : Ctx.t) ~pp_ack ~pp_answer ~pp_err ~pp_feed (cmd : sertop_cmd) : Ctx.t =
  let out = ctx.out_fmt in
  (* Collect terminated children *)
  let () =
    try
      let _pid, _status = Unix.waitpid [Unix.WNOHANG] (-1) in
      ()
    with
      Unix.Unix_error(Unix.ECHILD, _, _) ->
      (* No children for now *)
      ()
  in
  match cmd with
  | SerApi (cmd_tag, cmd) ->
    pp_ack out cmd_tag;
    let ans, st = SP.exec_cmd ctx.st cmd in
    List.iter (pp_answer out) @@ List.map (fun a -> SP.Answer (cmd_tag, a)) ans;
    { ctx with st }
  | Fork { fifo_in ; fifo_out } ->
    let pid = Unix.fork () in
    if pid = 0 then begin
      (* Children: close previous channels *)
      Stdlib.close_in ctx.in_chan;
      Format.pp_print_flush ctx.out_fmt ();
      Stdlib.close_out ctx.out_chan;
      (* Create new ones *)
      let () = Unix.mkfifo fifo_in 0o640 in
      let in_chan = Stdlib.open_in fifo_in in
      let () = Unix.mkfifo fifo_out 0o640 in
      let out_chan = Stdlib.open_out fifo_out in
      let out_fmt = Format.formatter_of_out_channel out_chan in
      Sertop_init.update_fb_handler ~pp_feed out_fmt;
      { ctx with in_chan; out_chan; out_fmt }
    end
    else
      (* Parent *)
      let () = pp_err out Sexp.(List [Atom "Forked"; Atom (string_of_int pid)]) in
      ctx
  | Quit ->
    ctx

let ser_loop ser_opts =

  (* Create closures for printers given initial options *)
  let pp_answer = out_answer ser_opts in
  let pp_err    = out_sexp ser_opts   in

  (* XXX EG: I don't understand this well, why is this lock needed ??
     Review fork code in CoqworkmgrApi *)
  let pr_mutex     = Mutex.create ()                                   in
  let ser_lock f x = Mutex.lock   pr_mutex;
                     f x;
                     Mutex.unlock pr_mutex                             in

  (* Wrap printers  *)
  let pp_answer out  = ser_lock (pp_answer out) in
  let pp_err    out  = ser_lock (pp_err out)    in
  let pp_ack out cid = pp_answer out (SP.Answer (cid, SP.Ack)) in
  let pp_opt fb = Sertop_util.feedback_opt_filter fb           in
  let pp_feed out fb =
    Option.iter (fun fb -> pp_answer out (SP.Feedback (Sertop_util.feedback_tr fb))) (pp_opt fb) in

  let ldir = Option.map Serapi.Serapi_paths.dirpath_of_file ser_opts.topfile in
  let ctx = Ctx.make
      ?in_file:ser_opts.topfile ?ldir ~cmd_id:0 ~in_chan:ser_opts.in_chan ~out_chan:ser_opts.out_chan () in

  (* Init Coq *)
  let () = Sertop_init.(
      coq_init
        { fb_handler   = pp_feed
        ; ml_load      = None
        ; debug        = ser_opts.debug
        ; allow_sprop  = ser_opts.allow_sprop
        ; indices_matter = ser_opts.indices_matter
        }) ctx.out_fmt
  in

  (* Follow the same approach than coqtop for now: allow Coq to be
   * interrupted by Ctrl-C. Not entirely safe or race free... but we
   * trust the IDEs to send the signal on coherent IO state.
   *)
  Sys.catch_break true;

  let injections =
    if ser_opts.no_prelude then []
    else [Coqargs.RequireInjection ("Coq.Init.Prelude", None, Some false)] in

  let _ml_load_path, _vo_load_path = ser_opts.ml_path, ser_opts.vo_path in
  let stm_options = Sertop_init.process_stm_flags ser_opts.async in

  if not ser_opts.no_init then begin
    let ndoc = { Stm.doc_type = doc_type ser_opts.topfile
               ; injections
               (* ; ml_load_path
                * ; vo_load_path *)
               ; stm_options
               } in
    let _ = Stm.new_doc ndoc in
    ()
  end;

  let incr_cmdid (ctx : Ctx.t) =
    { ctx with cmd_id = ctx.cmd_id + 1 } in

  (* Main loop *)
  let rec loop ctx =
    let quit, ctx =
      try
        let scmd = read_cmd ~ctx ~pp_err in
        ( is_cmd_quit scmd
        , process_serloop_cmd ~ctx ~pp_ack ~pp_answer ~pp_err ~pp_feed scmd)
      with Sys.Break -> false, ctx
    in
    if quit then () else (loop [@ocaml.tailcall]) (incr_cmdid ctx)
  in loop ctx
