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
open Ppx_python_runtime_serapi

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
module Vmemitcodes = Ser_vmemitcodes
module Retroknowledge = Ser_retroknowledge

type template_arity =
  [%import: Declarations.template_arity]
  [@@deriving sexp,python]

type ('a, 'b) declaration_arity =
  [%import: ('a, 'b) Declarations.declaration_arity]
  [@@deriving sexp,python]

type nested_type =
  [%import: Declarations.nested_type]
  [@@deriving sexp,python]

type recarg =
  [%import: Declarations.recarg]
  [@@deriving sexp,python]

type wf_paths =
  [%import: Declarations.wf_paths]
  [@@deriving sexp,python]

type regular_inductive_arity =
  [%import: Declarations.regular_inductive_arity
  [@with Term.sorts := Sorts.t;]]
  [@@deriving sexp,python]

type inductive_arity =
  [%import: Declarations.inductive_arity]
  [@@deriving sexp,python]

type one_inductive_body =
  [%import: Declarations.one_inductive_body]
  [@@deriving sexp,python]

type set_predicativity =
  [%import: Declarations.set_predicativity]
  [@@deriving sexp,python]

type engagement =
  [%import: Declarations.engagement]
  [@@deriving sexp,python]

type inline =
  [%import: Declarations.inline]
  [@@deriving sexp,python]

type universes =
  [%import: Declarations.universes]
  [@@deriving sexp,python]

type ('a, 'b) constant_def =
  [%import: ('a, 'b) Declarations.constant_def]
  [@@deriving sexp,python]

type typing_flags =
  [%import: Declarations.typing_flags]
  [@@deriving sexp,python]

type 'a constant_body =
  [%import: 'a Declarations.constant_body]
  [@@deriving sexp,python]

let sexp_of_constant_body f e =
  (* We cannot handle VM values *)
  sexp_of_constant_body f { e with const_body_code = None }

(* XXX: At least one serializer can be done *)
let sexp_of_module_retroknowledge _ =
  Serlib_base.sexp_of_opaque ~typ:"Declarations.module_retroknowledge"

let module_retroknowledge_of_sexp _ =
  Serlib_base.opaque_of_sexp ~typ:"Declarations.module_retroknowledge"

let _python_of_module_retroknowledge _ =
  Serlib_base.python_of_opaque ~typ:"Declarations.module_retroknowledge"

let _module_retroknowledge_of_python _ =
  Serlib_base.opaque_of_python ~typ:"Declarations.module_retroknowledge"

(* type abstract_inductive_universes =
 *   [%import: Declarations.abstract_inductive_universes]
 *   [@@deriving sexp] *)

type recursivity_kind =
  [%import: Declarations.recursivity_kind]
  [@@deriving sexp,yojson,python]

type record_info =
  [%import: Declarations.record_info]
  [@@deriving sexp,python]

type template_universes =
  [%import: Declarations.template_universes]
  [@@deriving sexp,yojson,python]

type mutual_inductive_body =
  [%import: Declarations.mutual_inductive_body
  [@with Context.section_context := Context.Named.t;]]
  [@@deriving sexp,python]

type ('ty,'a) functorize =
  [%import: ('ty, 'a) Declarations.functorize]
  [@@deriving sexp,python]

type with_declaration =
  [%import: Declarations.with_declaration]
  [@@deriving sexp,python]

type module_alg_expr =
  [%import: Declarations.module_alg_expr]
  [@@deriving sexp,python]

type structure_field_body =
  [%import: Declarations.structure_field_body]

and structure_body =
  [%import: Declarations.structure_body]

and module_signature =
  [%import: Declarations.module_signature]

and module_expression =
  [%import: Declarations.module_expression]

and module_implementation =
  [%import: Declarations.module_implementation]

and 'a generic_module_body =
  [%import: 'a Declarations.generic_module_body]

and module_body =
  [%import: Declarations.module_body]

and module_type_body =
  [%import: Declarations.module_type_body]
  [@@deriving sexp]
(* Strange error, need to recheck what is going on *)
(* [@@deriving sexp,python] *)

let python_of_module_body =
  Serlib_base.python_of_opaque ~typ:"module_body"
let module_body_of_python =
  Serlib_base.opaque_of_python ~typ:"module_body"
let python_of_module_type_body =
  Serlib_base.python_of_opaque ~typ:"module_type_body"
let module_type_body_of_python =
  Serlib_base.opaque_of_python ~typ:"module_type_body"
