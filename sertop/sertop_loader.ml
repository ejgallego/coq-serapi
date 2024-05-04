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

let debug = false

let list_last l = List.(nth l (length l - 1))

(* Should improve *)
let map_serlib fl_pkg =
  let supported = match fl_pkg with
    (* Linked-in statically *)
    | "coq-core.plugins.ltac." -> false
    (* | "tauto_plugin" -> false *)
    (* Supported *)
    | "coq-core.plugins.cc"               (* cc  *)
    | "coq-core.plugins.extraction"       (* extraction  *)
    | "coq-core.plugins.firstorder"       (* firstorder  *)
    | "coq-core.plugins.funind"           (* funind      *)
    | "coq-core.plugins.ltac2"            (* ltac2       *)
    | "coq-core.plugins.micromega"        (* micromega   *)
    | "coq-core.plugins.ring"             (* ring        *)
    | "coq-core.plugins.ssreflect"        (* ssreflect   *)
    | "coq-core.plugins.ssrmatching"      (* ssrmatching *)
    | "coq-core.plugins.number_string_notation" (* syntax *)
    | "coq-core.plugins.tauto"            (* tauto *)
    | "coq-core.plugins.zify"             (* zify *)
      -> true
    | _ ->
      if debug then Format.eprintf "missing serlib: %s@\n%!" fl_pkg;
      false
  in
  if supported
  then
    let plugin_name = String.split_on_char '.' fl_pkg |> list_last in
    Some ("coq-serapi.serlib." ^ plugin_name)
  else None

let plugin_handler user_handler =
  let loader = Option.default (Fl_dynload.load_packages ~debug:false) user_handler in
  fun fl_pkg ->
    try
      (* In 8.10 with a Dune-built Coq Fl_dynload will track the dependencies *)
      let fl_pkg = Mltop.PluginSpec.to_package fl_pkg in
      match map_serlib fl_pkg with
      | Some serlib_pkg ->
        if debug then
          Format.eprintf "[plugin loader]: plugin %s requested via findlib@\n%!" fl_pkg;
        loader [serlib_pkg]
      | None ->
        if debug then
          Format.eprintf "[plugin loader]: plugin %s requested via mltop@\n%!" fl_pkg;
        loader [fl_pkg]
    with
    | Dynlink.Error err as exn ->
      let msg = Dynlink.error_message err in
      Format.eprintf "[sertop] Critical Dynlink error %s@\n%!" msg;
      raise exn
    | Fl_package_base.No_such_package (pkg, _) as exn ->
      Format.eprintf "[sertop] Couldn't find the SerAPI plugin %s@; please check `ocamlfind list` does include SerAPI's plugin libraries.\n%!" pkg;
      raise exn
