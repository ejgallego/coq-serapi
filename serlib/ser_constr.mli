(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type metavariable = Constr.metavariable

val metavariable_of_sexp : Sexp.t -> metavariable
val sexp_of_metavariable : metavariable -> Sexp.t

type pconstant = Constr.pconstant

val pconstant_of_sexp : Sexp.t -> pconstant
val sexp_of_pconstant : pconstant -> Sexp.t

type pinductive = Constr.pinductive

val pinductive_of_sexp : Sexp.t -> pinductive
val sexp_of_pinductive : pinductive -> Sexp.t

type pconstructor = Constr.pconstructor

val pconstructor_of_sexp : Sexp.t -> pconstructor
val sexp_of_pconstructor : pconstructor -> Sexp.t

type cast_kind = Constr.cast_kind [@@deriving sexp,yojson,python,hash,compare]
type case_style = Constr.case_style [@@deriving sexp,yojson,python,hash,compare]

type case_printing = Constr.case_printing

val case_printing_of_sexp : Sexp.t -> case_printing
val sexp_of_case_printing : case_printing -> Sexp.t

type case_info = Constr.case_info

val case_info_of_sexp : Sexp.t -> case_info
val sexp_of_case_info : case_info -> Sexp.t

type rec_declaration = Constr.rec_declaration

val rec_declaration_of_sexp : Sexp.t -> rec_declaration
val sexp_of_rec_declaration : rec_declaration -> Sexp.t

type fixpoint = Constr.fixpoint

val fixpoint_of_sexp : Sexp.t -> fixpoint
val sexp_of_fixpoint : fixpoint -> Sexp.t

type cofixpoint = Constr.cofixpoint

val cofixpoint_of_sexp : Sexp.t -> cofixpoint
val sexp_of_cofixpoint : cofixpoint -> Sexp.t

type 'constr pexistential = 'constr Constr.pexistential
  [@@deriving sexp, yojson, python, hash, compare]

type ('constr, 'types) prec_declaration = ('constr, 'types) Constr.prec_declaration

val prec_declaration_of_sexp :
  (Sexp.t -> 'constr) -> (Sexp.t -> 'types) ->
  Sexp.t -> ('constr, 'types) prec_declaration
val sexp_of_prec_declaration :
  ('constr -> Sexp.t) -> ('types -> Sexp.t) ->
  ('constr, 'types) prec_declaration -> Sexp.t

type ('constr, 'types) pfixpoint = ('constr, 'types) Constr.pfixpoint

val pfixpoint_of_sexp :
  (Sexp.t -> 'constr) ->
  (Sexp.t -> 'types) -> Sexp.t -> ('constr, 'types) pfixpoint

val sexp_of_pfixpoint :
  ('constr -> Sexp.t) ->
  ('types -> Sexp.t) -> ('constr, 'types) pfixpoint -> Sexp.t

type ('constr, 'types) pcofixpoint = ('constr, 'types) Constr.pcofixpoint

val pcofixpoint_of_sexp :
  (Sexp.t -> 'constr) -> (Sexp.t -> 'types) ->
  Sexp.t -> ('constr, 'types) pcofixpoint

val sexp_of_pcofixpoint :
  ('constr -> Sexp.t) -> ('types -> Sexp.t) ->
  ('constr, 'types) pcofixpoint -> Sexp.t

type t = Constr.t
  [@@deriving sexp,yojson,hash,compare]

val t_of_python : Py.Object.t -> t
val python_of_t : t -> Py.Object.t

type constr = t
  [@@deriving sexp,yojson,hash,compare]

val constr_of_python : Py.Object.t -> constr
val python_of_constr : constr -> Py.Object.t

type types  = constr
  [@@deriving sexp,yojson,hash,compare]

val types_of_python : Py.Object.t -> types
val python_of_types : types -> Py.Object.t

type existential = Constr.existential
val existential_of_sexp : Sexp.t -> existential
val sexp_of_existential : existential -> Sexp.t

type sorts_family = Sorts.family
val sorts_family_of_sexp : Sexp.t -> sorts_family
val sexp_of_sorts_family : sorts_family -> Sexp.t

type named_declaration = Constr.named_declaration
val named_declaration_of_sexp : Sexp.t -> named_declaration
val sexp_of_named_declaration : named_declaration -> Sexp.t
val named_declaration_of_python : Py.Object.t -> named_declaration
val python_of_named_declaration : named_declaration -> Py.Object.t

type named_context = Constr.named_context
  [@@deriving sexp,yojson,python,hash,compare]

type rel_declaration = Constr.rel_declaration
val rel_declaration_of_sexp : Sexp.t -> rel_declaration
val sexp_of_rel_declaration : rel_declaration -> Sexp.t
val rel_declaration_of_python : Py.Object.t -> rel_declaration
val python_of_rel_declaration : rel_declaration -> Py.Object.t

type rel_context = Constr.rel_context
  [@@deriving sexp,yojson,python,hash,compare]
