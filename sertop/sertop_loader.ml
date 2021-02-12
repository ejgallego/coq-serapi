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
(* Copyright 2016-2019 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let debug = false
let ml_path = ref []

let add_ml_path path =
  ml_path := path :: !ml_path

(* Should improve *)
let map_serlib ml_mod =
  let plugin_name = Filename.(remove_extension (basename ml_mod)) in
  let supported = match plugin_name with
    (* Linked-in statically *)
    | "ltac_plugin" -> false
    (* | "tauto_plugin" -> false *)
    (* Supported *)
    | "ground_plugin"           (* firstorder *)
    | "recdef_plugin"           (* funind *)
    | "ring_plugin"             (* setoid_ring *)
    | "extraction_plugin"       (* setoid_ring *)
    | "ssrmatching_plugin"      (* ssrmatching *)
    | "ssreflect_plugin"        (* ssr *)
      -> true
    | _ ->
      if debug then Format.eprintf "missing serlib: %s@\n%!" ml_mod;
      false
  in
  if supported
  then Some ("coq-serapi.serlib." ^ plugin_name)
  else None

let plugin_handler user_handler =
  let loader = Option.default Dynlink.loadfile user_handler in
  fun ml_mod ->
    try
      (* In 8.10 with a Dune-built Coq Fl_dynload will track the dependencies *)
      match map_serlib ml_mod with
      | Some serlib_pkg ->
        if debug then
          Format.eprintf "[plugin loader]: module %s requested via findlib@\n%!" ml_mod;
        Fl_dynload.load_packages [serlib_pkg]
      | None ->
        if debug then
          Format.eprintf "[plugin loader]: module %s requested via mltop@\n%!" ml_mod;
        let _, ml_file = System.find_file_in_path ~warn:true !ml_path ml_mod in
        let () = loader ml_file in
        ()
    with
      Dynlink.Error err ->
      let msg = Dynlink.error_message err in
      Format.eprintf "[sertop] Critical Dynlink error %s@\n%!" msg
