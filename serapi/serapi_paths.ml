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

let coq_loadpath_default ~implicit ~coq_path =
  let open Loadpath in
  let mk_path prefix = coq_path ^ "/" ^ prefix in
  let mk_core_path prefix = coq_path ^ "/../coq-core/" ^ prefix in
  (* let mk_ml = () in *)
  let mk_vo ~has_ml ~coq_path ~dir ~implicit ~absolute =
    { unix_path = if absolute then dir else mk_path dir
    ; coq_path
    ; has_ml
    ; recursive = true
    ; implicit
    }
  in
  (* in 8.8 we can use Libnames.default_* *)
  let coq_root     = Names.DirPath.make [Libnames.coq_root] in
  let default_root = Libnames.default_root_prefix in
  let ml_paths =
    let plugins_path = mk_core_path "plugins" in
    (* Format.eprintf "plugins_dirs: %s@\n%!" plugins_path; *)
    let plugins_dirs = System.all_subdirs ~unix_path:plugins_path in
    List.map fst plugins_dirs
  in
  ml_paths ,
  [ mk_vo ~has_ml:false ~coq_path:coq_root     ~implicit       ~dir:"theories" ~absolute:false
  ; mk_vo ~has_ml:true  ~coq_path:default_root ~implicit:false ~dir:"user-contrib" ~absolute:false;
  ] @
  List.map (fun dir -> mk_vo ~has_ml:true ~coq_path:default_root ~implicit:false ~dir ~absolute:true)
    Envars.coqpath

(******************************************************************************)
(* Generate a module name given a file                                        *)
(******************************************************************************)
let dirpath_of_file f =
  let ldir0 =
    try
      let lp = Loadpath.find_load_path (Filename.dirname f) in
      Loadpath.logical lp
    with Not_found -> Libnames.default_root_prefix
  in
  let file = Filename.chop_extension (Filename.basename f) in
  let id = Names.Id.of_string file in
  Libnames.add_dirpath_suffix ldir0 id
