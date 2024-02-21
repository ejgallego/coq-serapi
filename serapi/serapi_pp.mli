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

(** This module includes all of sertop custom Format-based printers
    for Coq datatypes.

    We may want to split it into a library at some point and replace
    parts of Coq printing/
*)

type 'a pp = Format.formatter -> 'a -> unit

val pp_str      :                            string   pp
val pp_opt      :                'a pp -> ('a option) pp
val pp_list     : ?sep:string -> 'a pp -> ('a list)   pp

val pp_stateid  : Stateid.t         pp
val pp_feedback : Feedback.feedback pp
val pp_xml      : Xml_datatype.xml  pp
