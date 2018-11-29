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

(************************************************************************)
(* Global Protocol Options                                              *)
(************************************************************************)

type ser_opts = {
  (* Input output Options *)
  in_chan  : in_channel;        (* Input/Output channels                      *)
  out_chan : out_channel;
                                (* Printers                                   *)
  printer  : Sertop_ser.ser_printer;

  debug    : bool;
  print0   : bool;
  lheader  : bool;              (* Print lenght header (deprecated)           *)

  (* Coq options *)
  no_init  : bool;              (* Whether to create the initial document     *)
  coq_path : string;            (* Coq standard library location              *)
  std_impl : bool;              (* Whether the standard library should be loaded with implicit paths *)
                                (* -R and -Q options                          *)
  loadpath : Mltop.coq_path list; (* From -R and -Q options usually *)
  async    : Sertop_init.async_flags;
}

(******************************************************************************)
(* Input/Output -- Main Loop                                                  *)
(******************************************************************************)

(** [ser_loop opts] main se(xp)r-protocol loop *)
val ser_loop : ser_opts -> unit
