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

open Sexplib.Std
open Ppx_python_runtime
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

(* let python_of_unit _ = Py.Int.of_int 0
 * let unit_of_python _ = () *)

let hash_fold_array = hash_fold_array_frozen

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
  [@@deriving sexp,yojson,python,hash,compare]

type ('a, 'b) declaration_arity =
  [%import: ('a, 'b) Declarations.declaration_arity]
  [@@deriving sexp,yojson,python,hash,compare]

type nested_type =
  [%import: Declarations.nested_type]
  [@@deriving sexp,yojson,python,hash,compare]

type recarg =
  [%import: Declarations.recarg]
  [@@deriving sexp,yojson,python,hash,compare]

type wf_paths =
  [%import: Declarations.wf_paths]
  [@@deriving sexp,yojson,python,hash,compare]

type regular_inductive_arity =
  [%import: Declarations.regular_inductive_arity
  [@with Term.sorts := Sorts.t;]]
  [@@deriving sexp,yojson,python,hash,compare]

type inductive_arity =
  [%import: Declarations.inductive_arity]
  [@@deriving sexp,yojson,python,hash,compare]

type one_inductive_body =
  [%import: Declarations.one_inductive_body]
  [@@deriving sexp,yojson,python,hash,compare]

(* type set_predicativity =
 *   [%import: Declarations.set_predicativity]
 *   [@@deriving sexp] *)

(* type engagement =
 *   [%import: Declarations.engagement]
 *   [@@deriving sexp] *)

type inline =
  [%import: Declarations.inline]
  [@@deriving sexp,yojson,python,hash,compare]

type universes =
  [%import: Declarations.universes]
  [@@deriving sexp,yojson,python,hash,compare]

type ('a, 'b) constant_def =
  [%import: ('a, 'b) Declarations.constant_def]
  [@@deriving sexp,yojson,python,hash,compare]

type typing_flags =
  [%import: Declarations.typing_flags]
  [@@deriving sexp,yojson,python,hash,compare]

(* type work_list =
 *   [%import: Declarations.work_list]
 *   [@@deriving sexp] *)

(* type abstr_info =
 *   [%import: Declarations.abstr_info]
 *   [@@deriving sexp] *)

(* type cooking_info =
 *   [%import: Declarations.cooking_info]
 *   [@@deriving sexp] *)

type 'a pconstant_body =
  [%import: 'a Declarations.pconstant_body]
  [@@deriving sexp,yojson,python,hash,compare]

type constant_body =
  [%import: Declarations.constant_body]
  [@@deriving sexp,yojson,python,hash,compare]

let sexp_of_constant_body e =
  (* We cannot handle VM values *)
  sexp_of_constant_body { e with const_body_code = None }

module MRK = struct
  type 'a t = 'a Declarations.module_retroknowledge
  let name = "Declarations.module_retroknowledge"
end

module B_ = SerType.Opaque1(MRK)

type 'a module_retroknowledge = 'a B_.t
let sexp_of_module_retroknowledge = B_.sexp_of_t
let module_retroknowledge_of_sexp = B_.t_of_sexp
let _python_of_module_retroknowledge = B_.python_of_t
let _module_retroknowledge_of_python = B_.t_of_python
let module_retroknowledge_of_yojson = B_.of_yojson
let module_retroknowledge_to_yojson = B_.to_yojson
let hash_fold_module_retroknowledge = B_.hash_fold_t
let compare_module_retroknowledge = B_.compare

type recursivity_kind =
  [%import: Declarations.recursivity_kind]
  [@@deriving sexp,yojson,python,hash,compare]

type record_info =
  [%import: Declarations.record_info]
  [@@deriving sexp,yojson,python,hash,compare]

type template_universes =
  [%import: Declarations.template_universes]
  [@@deriving sexp,yojson,python,hash,compare]

type mutual_inductive_body =
  [%import: Declarations.mutual_inductive_body
  [@with Context.section_context := Context.Named.t;]]
  [@@deriving sexp,yojson,python,hash,compare]

type ('ty,'a) functorize =
  [%import: ('ty, 'a) Declarations.functorize]
  [@@deriving sexp,yojson,python,hash,compare]

type 'a with_declaration =
  [%import: 'a Declarations.with_declaration]
  [@@deriving sexp,yojson,python,hash,compare]

type 'a module_alg_expr =
  [%import: 'a Declarations.module_alg_expr]
  [@@deriving sexp,yojson,python,hash,compare]

type structure_field_body =
  [%import: Declarations.structure_field_body]
  [@@deriving sexp,yojson,hash,compare]

and structure_body =
  [%import: Declarations.structure_body]
  [@@deriving sexp,yojson,hash,compare]

and module_signature =
  [%import: Declarations.module_signature]
  [@@deriving sexp,yojson,hash,compare]

and module_expression =
  [%import: Declarations.module_expression]
  [@@deriving sexp,yojson,hash,compare]

and module_implementation =
  [%import: Declarations.module_implementation]
  [@@deriving sexp,yojson,hash,compare]

and 'a generic_module_body =
  [%import: 'a Declarations.generic_module_body]
  [@@deriving sexp,yojson,hash,compare]

and module_body =
  [%import: Declarations.module_body]
  [@@deriving sexp,yojson,hash,compare]

and module_type_body =
  [%import: Declarations.module_type_body]
  [@@deriving sexp,yojson,hash,compare]

let structure_body_of_python = Obj.magic 0
let python_of_structure_body = Obj.magic 0
let module_body_of_python = Obj.magic 0
let python_of_module_body = Obj.magic 0
let module_type_body_of_python = Obj.magic 0
let python_of_module_type_body = Obj.magic 0
