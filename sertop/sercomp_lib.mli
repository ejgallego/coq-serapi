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

type procfun
  =  doc:Stm.doc
  -> sid:Stateid.t
  -> Vernacexpr.vernac_control CAst.t
  -> Stm.doc * Stateid.t

type compfun
  =  in_file:string
  -> in_chan:in_channel
  -> process:procfun
  -> doc:Stm.doc
  -> sid:Stateid.t
  -> Stm.doc

val maincomp
  :  ext:string
  -> name:string
  -> desc:string
  -> compfun:compfun
  -> unit
