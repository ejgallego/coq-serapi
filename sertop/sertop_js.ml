(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API -- Coq Javascript Worker                       *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib
open Sertop_async

(* Send answer to the main thread *)
let post_message (msg : Sexp.t) : unit =
  let msg_str = Js.string (Sexp.to_string msg) in
  Worker.post_message msg_str

(* Receive message from the main thread *)
let on_message = sertop_callback post_message

(* Special JS ML toplevel*)
let jstop : Mltop.toplevel =
  let open Mltop in
  {
    load_obj = Sertop_jslib.coq_cma_link;
    (* We ignore all the other operations for now *)
    use_file = (fun _ -> ());
    add_dir  = (fun _ -> ());
    ml_loop  = (fun _ -> ());
  }

let setup_pseudo_fs () =
  Sys_js.register_autoload ~path:"/" (fun (_,s) -> Sertop_jslib.coq_vo_req s)

let setup_std_printers out_fn =
  Sys_js.set_channel_flusher stdout (fun msg -> out_fn @@ Sexp.(List [Atom "StdOut"; Atom msg]));
  Sys_js.set_channel_flusher stderr (fun msg -> out_fn @@ Sexp.(List [Atom "StdErr"; Atom msg]));
  ()

open Sexplib.Conv

type progress_info =
  [%import: Sertop_jslib.progress_info]
  [@@deriving sexp]

type _digest = string
  [@@deriving sexp]

type digest = Digest.t
let digest_of_sexp s = Digest.from_hex (_digest_of_sexp s)
let sexp_of_digest d = sexp_of__digest (Digest.to_hex d)

type coq_pkg =
  [%import: Jslib.coq_pkg
  [@with
     Digest.t := digest;
  ]]
  [@@deriving sexp]

type coq_bundle =
  [%import: Jslib.coq_bundle]
  [@@deriving sexp]

type lib_event =
  [%import: Sertop_jslib.lib_event
  [@with
     Jslib.coq_bundle := coq_bundle;
  ]]
  [@@deriving sexp]

(* This code is executed on Worker initialization *)
let _ =
  let on_msg str =
    try
      let cmd = Sexp.of_string (Js.to_string str) in
      on_message cmd
    with _ ->
      Worker.post_message (Js.string "Error in input conversion")
  in
  Worker.set_onmessage on_msg;

  setup_pseudo_fs    ();
  setup_std_printers post_message;

  (* Before Coq Init (XXX: Is this the proper place?) *)
  Mltop.set_top jstop;
  Format.eprintf "Initializing Coq, please wait for the libraries to download@\n%!";

  (* XXX: Run this in the Lwt.monad *)
  let open Lwt in
  async (fun () ->
      let base_path = "./"                                      in
      let pkg       = "init"                                    in
      let out_libevent lb = post_message (sexp_of_lib_event lb) in
      Sertop_jslib.load_pkg out_libevent base_path pkg          >>= fun () ->
      return (sertop_init post_message)
    );
  (* Library init *)
  ()
