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
  -> in_file:string
  -> unit

type compfun
  =  mode:Sertop_arg.comp_mode
  -> pp:(Format.formatter -> Sexplib.Sexp.t -> unit)
  -> in_file:string
  -> doc:Stm.doc
  -> sid:Stateid.t
  -> Stm.doc

val maincomp
  :  ext:string
  -> name:string
  -> desc:string
  -> compfun:compfun
  -> unit
