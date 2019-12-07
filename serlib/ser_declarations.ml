(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv
open Declarations

module Rtree   = Ser_rtree
module Names   = Ser_names
module Context = Ser_context
module Constr  = Ser_constr
module Sorts   = Ser_sorts
module Univ    = Ser_univ
module CPrimitives = Ser_cPrimitives
module Vmvalues    = Ser_vmvalues
module Conv_oracle = Ser_conv_oracle
module Mod_subst   = Ser_mod_subst
module Opaqueproof = Ser_opaqueproof
module Cemitcodes  = Ser_cemitcodes
module Retroknowledge = Ser_retroknowledge

type template_arity =
  [%import: Declarations.template_arity]
  [@@deriving sexp]

type ('a, 'b) declaration_arity =
  [%import: ('a, 'b) Declarations.declaration_arity]
  [@@deriving sexp]

type recarg =
  [%import: Declarations.recarg]
  [@@deriving sexp]

type wf_paths =
  [%import: Declarations.wf_paths]
  [@@deriving sexp]

type regular_inductive_arity =
  [%import: Declarations.regular_inductive_arity
  [@with Term.sorts := Sorts.t;]]
  [@@deriving sexp]

type inductive_arity =
  [%import: Declarations.inductive_arity]
  [@@deriving sexp]

type one_inductive_body =
  [%import: Declarations.one_inductive_body]
  [@@deriving sexp]

type set_predicativity =
  [%import: Declarations.set_predicativity]
  [@@deriving sexp]

type engagement =
  [%import: Declarations.engagement]
  [@@deriving sexp]

type inline =
  [%import: Declarations.inline]
  [@@deriving sexp]

type universes =
  [%import: Declarations.universes]
  [@@deriving sexp]

type ('a, 'b) constant_def =
  [%import: ('a, 'b) Declarations.constant_def]
  [@@deriving sexp]

type typing_flags =
  [%import: Declarations.typing_flags]
  [@@deriving sexp]

type 'a constant_body =
  [%import: 'a Declarations.constant_body]
  [@@deriving sexp]

let sexp_of_constant_body f e =
  (* We cannot handle VM values *)
  sexp_of_constant_body f { e with const_body_code = None }

(* XXX: At least one serializer can be done *)
let sexp_of_module_retroknowledge _ =
  Serlib_base.sexp_of_opaque ~typ:"Declarations.module_retroknowledge"

let module_retroknowledge_of_sexp _ =
  Serlib_base.opaque_of_sexp ~typ:"Declarations.module_retroknowledge"

(* type abstract_inductive_universes =
 *   [%import: Declarations.abstract_inductive_universes]
 *   [@@deriving sexp] *)

type recursivity_kind =
  [%import: Declarations.recursivity_kind]
  [@@deriving sexp,yojson]

type record_info =
  [%import: Declarations.record_info]
  [@@deriving sexp]

type mutual_inductive_body =
  [%import: Declarations.mutual_inductive_body
  [@with Context.section_context := Context.Named.t;]]
  [@@deriving sexp]

type ('ty,'a) functorize =
  [%import: ('ty, 'a) Declarations.functorize]
  [@@deriving sexp]

type with_declaration =
  [%import: Declarations.with_declaration]
  [@@deriving sexp]

type module_alg_expr =
  [%import: Declarations.module_alg_expr]
  [@@deriving sexp]

type structure_field_body =
  [%import: Declarations.structure_field_body]
  [@@deriving sexp]

and structure_body =
  [%import: Declarations.structure_body]
  [@@deriving sexp]

and module_signature =
  [%import: Declarations.module_signature]
  [@@deriving sexp]

and module_expression =
  [%import: Declarations.module_expression]
  [@@deriving sexp]

and module_implementation =
  [%import: Declarations.module_implementation]
  [@@deriving sexp]

and 'a generic_module_body =
  [%import: 'a Declarations.generic_module_body]
  [@@deriving sexp]

and module_body =
  [%import: Declarations.module_body]
  [@@deriving sexp]

and module_type_body =
  [%import: Declarations.module_type_body]
  [@@deriving sexp]
