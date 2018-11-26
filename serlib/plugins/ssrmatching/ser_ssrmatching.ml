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
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std

type cpattern =
  [%import: Ssrmatching_plugin.Ssrmatching.cpattern]

(* XXX *)
type _cpattern = char * Ser_genintern.glob_constr_and_expr * Ser_geninterp.interp_sign option
  [@@deriving sexp]

let cpattern_of_sexp o = Obj.magic (_cpattern_of_sexp o)
let sexp_of_cpattern o = sexp_of__cpattern Obj.(magic o)

type ('a, 'b) ssrpattern =
  [%import: ('a, 'b) Ssrmatching_plugin.Ssrmatching.ssrpattern]
  [@@deriving sexp]

type _rpattern = (cpattern, cpattern) ssrpattern
  [@@deriving sexp]

type rpattern =
  [%import: Ssrmatching_plugin.Ssrmatching.rpattern]

let rpattern_of_sexp o = Obj.magic (_rpattern_of_sexp o)
let sexp_of_rpattern o = sexp_of__rpattern Obj.(magic o)

type ssrdir =
  [%import: Ssrmatching_plugin.Ssrmatching.ssrdir]
  [@@deriving sexp]
