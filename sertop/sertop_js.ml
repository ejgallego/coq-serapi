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
open Js_of_ocaml

open Jscoq_lib

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
    load_obj = Jslibmng.coq_cma_link;
    (* We ignore all the other operations for now *)
    use_file = (fun _ -> ());
    add_dir  = (fun _ -> ());
    ml_loop  = (fun _ -> ());
  }

let setup_pseudo_fs () =
  Sys_js.unmount ~path:"/static";
  Sys_js.mount ~path:"/static/" (fun ~prefix ~path -> ignore(prefix); Jslibmng.coq_vo_req path)

let setup_std_printers out_fn =
  Sys_js.set_channel_flusher stdout (fun msg -> out_fn @@ Sexp.(List [Atom "StdOut"; Atom msg]));
  Sys_js.set_channel_flusher stderr (fun msg -> out_fn @@ Sexp.(List [Atom "StdErr"; Atom msg]));
  ()

open Sexplib.Conv

module Yojson = struct
  module Safe = struct
    type t = Yojson.Safe.t
    let t_of_sexp _ = `String "XXX"
    let sexp_of_t _ = Sexp.Atom "XXX"
  end
end

type progress_info =
  [%import: Jscoq_lib.Jslibmng.progress_info]
  [@@deriving sexp]

type digest =
  [%import: Digest.t]
  [@@deriving sexp]

type coq_pkg =
  [%import: Jscoq_lib.Jslib.coq_pkg
  [@with
     Stdlib.Digest.t := digest;
  ]]
  [@@deriving sexp]

type coq_bundle =
  [%import: Jscoq_lib.Jslib.coq_bundle]
  [@@deriving sexp]

type lib_event =
  [%import: Jscoq_lib.Jslibmng.lib_event
  [@with
    Jscoq_lib.Jslib.coq_bundle := coq_bundle;
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

  setup_pseudo_fs    ();
  setup_std_printers post_message;

  (* Before Coq Init (XXX: Is this the proper place?) *)
  Mltop.set_top jstop;
  Format.eprintf "Initializing Coq, please wait for the libraries to download@\n%!";

  (* XXX: Run this in the Lwt.monad *)
  let open Lwt   in
  let open List  in
  async (fun () ->
      let out_libevent lb = post_message (sexp_of_lib_event lb) in
      let base_path = "./coq-pkgs/"                             in
      let pkgs      = ["init"] (*"peacoq"]*)                    in

      let _pkg_to_bb cp = Mltop.{
          recursive = false;
          path_spec = VoPath {
              coq_path  = Names.(DirPath.make @@ List.rev @@ List.map Id.of_string cp.pkg_id);
              unix_path = Jslib.to_dir cp;
              has_ml    = if length cp.cma_files > 0 then AddRecML else AddNoML;
              implicit  = false;
            }
        } in

      Lwt_list.map_s (Jslibmng.load_pkg out_libevent base_path) pkgs >>= fun _bundles ->
      (* let all_pkgs    = List.(concat @@ map (fun b -> b.pkgs) bundles)   in *)
      (* let iload_path  = List.map pkg_to_bb all_pkgs                      in *)
      let iload_path = [] in
      let require_libs= ["Coq.Init.Prelude", None, Some true]            in
      let debug       = false                                            in
      ignore (sertop_init ~fb_out:post_message ~iload_path ~require_libs ~debug);
      (* We only accept messages when Coq is ready.             *)
      Worker.set_onmessage on_msg;
      return_unit
    );
  (* Library init *)
  ()
