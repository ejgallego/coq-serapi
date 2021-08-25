(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API -- Async loop                                  *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib
open Serapi.Serapi_protocol

(* There a subtles differences between the sync and async loop, so we
   keep a bit of duplication for now. *)

let async_sid = ref 0

let read_cmd cmd_sexp : [`Error of Sexp.t | `Ok of string * cmd ] =
  try         `Ok (Sertop.Sertop_ser.tagged_cmd_of_sexp cmd_sexp)
  with _exn ->
    try
      let tag, cmd = string_of_int !async_sid, Sertop.Sertop_ser.cmd_of_sexp cmd_sexp in
      incr async_sid;
      `Ok (tag, cmd)
    with | exn ->
      `Error (Conv.sexp_of_exn exn)

(* Initialize Coq. *)
let sertop_init ~(fb_out : Sexp.t -> unit) ~ml_load_path:_ ~vo_load_path:_ ~injections ~debug ~allow_sprop =
  let open! Sertop.Sertop_init in

  let fb_handler _ fb = Sertop.Sertop_ser.sexp_of_answer (Feedback (Sertop.Sertop_util.feedback_tr fb)) |> fb_out in

  coq_init {
    fb_handler
  ; ml_load = None
  ; debug
  ; allow_sprop
  ; indices_matter = false
  } Format.std_formatter;

  let stm_options = process_stm_flags
    { enable_async  = None
    ; deep_edits    = false
    ; async_workers = 0
    ; error_recovery = false
    } in

  let open Stm in
  let doc_type = Interactive (TopLogical Names.(DirPath.make [Id.of_string "SerTopJS"])) in

  let ndoc = { doc_type
             ; injections
             (* ; ml_load_path
              * ; vo_load_path *)
             ; stm_options
             } in
  new_doc ndoc

let async_mut = Mutex.create ()

let st_ref = ref (State.make ())

(* Callback for a command. Trying to make it thread-safe. *)
let sertop_callback (out_fn : Sexp.t -> unit) sexp =
  Mutex.lock async_mut;
  let out_answer a = out_fn (Sertop.Sertop_ser.sexp_of_answer a) in
  let out_error  a = out_fn a                             in
  begin match read_cmd sexp with
  | `Error err         ->
    out_error  err
  | `Ok (cmd_tag, cmd) ->
    out_answer (Answer (cmd_tag, Ack));
    let ans, st = exec_cmd !st_ref cmd in
    List.(iter out_answer @@ map (fun a -> Answer (cmd_tag, a)) ans);
    st_ref := st
  end;
  Mutex.unlock async_mut
