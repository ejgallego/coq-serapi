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
open Sertop_arg

val create_from_file
  :  in_file:string
  -> async:string option
  -> iload_path:Mltop.coq_path list
  -> Stm.doc * Stateid.t

val process_vernac
  :  mode:comp_mode
  -> pp:(Format.formatter -> Sexp.t -> unit)
  -> doc:Stm.doc
  -> st:Stateid.t
  -> Vernacexpr.vernac_control CAst.t
  -> Stm.doc * Stateid.t

val close_document
  :  mode:comp_mode
  -> doc:Stm.doc
  -> out_vo:string
  -> unit

type compfun
  =  comp_mode
  -> bool
  -> Sertop_ser.ser_printer
  -> string option
  -> string
  -> Mltop.coq_path list
  -> Mltop.coq_path list
  -> Mltop.coq_path list
  -> string -> bool -> bool -> bool -> unit

val maincomp
  :  ext:string
  -> name:string
  -> desc:string
  -> compfun:compfun
  -> unit
