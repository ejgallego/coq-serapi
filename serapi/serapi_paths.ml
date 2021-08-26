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

(******************************************************************************)
(* Coq Prelude Loading Defaults (to be improved)                              *)
(******************************************************************************)

let coq_loadpath_default ~implicit ~coq_path =
  let open Loadpath in
  let mk_path prefix = coq_path ^ "/" ^ prefix in
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
    let plugins_dirs = System.all_subdirs ~unix_path:(mk_path "plugins") in
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
