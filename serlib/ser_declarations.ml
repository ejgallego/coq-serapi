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
open Sexplib.Conv

module Names   = Ser_names
module Context = Ser_context
module Constr  = Ser_constr
module Sorts   = Ser_sorts
module Univ    = Ser_univ
module Decl_kinds = Ser_decl_kinds
module Cbytecodes = Ser_cbytecodes
module Conv_oracle = Ser_conv_oracle

type template_arity =
  [%import: Declarations.template_arity]
  [@@deriving sexp]

type ('a, 'b) declaration_arity =
  [%import: ('a, 'b) Declarations.declaration_arity]
  [@@deriving sexp]

type recarg =
  [%import: Declarations.recarg]
  [@@deriving sexp]

(* XXX: Fixme *)
module Rtree = struct

  type 'a t = 'a Rtree.t

  let t_of_sexp f s = Rtree.mk_node (f s) [||]

  let sexp_of_t f t =
    let n, ll = Rtree.dest_node t in
    Sexp.(List [Atom "RTree"; f n; sexp_of_int @@ Array.length ll])

end

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

type projection_body =
  [%import: Declarations.projection_body
  [@with Names.mutual_inductive := Names.MutInd.t]]
  [@@deriving sexp]

type typing_flags =
  [%import: Declarations.typing_flags]
  [@@deriving sexp]

type record_body =
  [%import: Declarations.record_body
  [@with Context.section_context := Context.Named.t;]]
  [@@deriving sexp]

type abstract_inductive_universes =
  [%import: Declarations.abstract_inductive_universes]
  [@@deriving sexp]

type recursivity_kind =
  [%import: Declarations.recursivity_kind]
  [@@deriving sexp]

type mutual_inductive_body =
  [%import: Declarations.mutual_inductive_body
  [@with Context.section_context := Context.Named.t;]]
  [@@deriving sexp]

