(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Cmdliner

val prelude         : string Term.t
val async           : string option Term.t
val async_full      : bool Term.t
val deep_edits      : bool Term.t
val implicit_stdlib : bool Term.t
val rload_path      : (string * string) list Term.t
val load_path       : (string * string) list Term.t
val printer         : Sertop_sexp.ser_printer Term.t
val debug           : bool Term.t
val print0          : bool Term.t
val length          : bool Term.t
