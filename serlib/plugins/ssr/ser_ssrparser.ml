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
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv

module Ssrmatching = Ser_ssrmatching
open Ssrmatching

module Ltac_plugin = struct
  module Tacexpr = Ser_tacexpr
end

module Ssrast = Ser_ssrast

module Ssreflect_plugin = struct
  module Ssrast = Ser_ssrast
  module Ssrequality = Ser_ssrequality
  module Ssrparser = Ssreflect_plugin.Ssrparser
end

open! Ssrast

type t_movearg = (cpattern ssragens) ssrmovearg
[@@deriving sexp]

let ser_wit_ssrmovearg  =
  Ser_genarg.mk_uniform sexp_of_t_movearg t_movearg_of_sexp

let ser_wit_ssrapplyarg =
  Ser_genarg.mk_uniform sexp_of_ssrapplyarg ssrapplyarg_of_sexp

let ser_wit_clauses =
  Ser_genarg.mk_uniform sexp_of_clauses clauses_of_sexp

type t_rwarg = Ssreflect_plugin.Ssrequality.ssrrwarg list [@@deriving sexp]

let ser_wit_ssrrwargs =
  Ser_genarg.mk_uniform sexp_of_t_rwarg t_rwarg_of_sexp

type t_h1 = Ltac_plugin.Tacexpr.raw_tactic_expr fwdbinders
[@@deriving sexp]

type t_h2 = Ltac_plugin.Tacexpr.glob_tactic_expr fwdbinders
[@@deriving sexp]

type t_h3 = Geninterp.Val.t fwdbinders
[@@deriving sexp]

let ser_wit_ssrhavefwdwbinders =
  Ser_genarg.{
    raw_ser = sexp_of_t_h1;
    raw_des = t_h1_of_sexp;

    glb_ser = sexp_of_t_h2;
    glb_des = t_h2_of_sexp;

    top_ser = sexp_of_t_h3;
    top_des = t_h3_of_sexp;
  }

type ssrfwdview =
  [%import: Ssrparser.ssrfwdview]
  [@@deriving sexp]

type ssreqid =
  [%import: Ssrparser.ssreqid]
  [@@deriving sexp]

type ssrarg =
  [%import: Ssrparser.ssrarg]
  [@@deriving sexp]

let ser_wit_ssrarg =
  Ser_genarg.mk_uniform sexp_of_ssrarg ssrarg_of_sexp

type h_h1 = Ltac_plugin.Tacexpr.raw_tactic_expr ssrhint
[@@deriving sexp]
type h_h2 = Ltac_plugin.Tacexpr.glob_tactic_expr ssrhint
[@@deriving sexp]
type h_h3 = Geninterp.Val.t ssrhint
[@@deriving sexp]

let ser_wit_ssrhintarg =
  Ser_genarg.{
    raw_ser = sexp_of_h_h1;
    raw_des = h_h1_of_sexp;

    glb_ser = sexp_of_h_h2;
    glb_des = h_h2_of_sexp;

    top_ser = sexp_of_h_h3;
    top_des = h_h3_of_sexp;
  }
let register () =
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrapplyarg ser_wit_ssrapplyarg;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrarg ser_wit_ssrarg;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrcasearg  ser_wit_ssrmovearg;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrclauses  ser_wit_clauses;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrmovearg  ser_wit_ssrmovearg;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrhavefwdwbinders ser_wit_ssrhavefwdwbinders;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrhintarg ser_wit_ssrhintarg;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrrwargs   ser_wit_ssrrwargs;

(* Missing

  Ssreflect_plugin.Ssrparser.wit_ast_closure_lterm
  Ssreflect_plugin.Ssrparser.wit_ast_closure_term
  Ssreflect_plugin.Ssrparser.wit_ssr_idcomma
  Ssreflect_plugin.Ssrparser.wit_ssragen
  Ssreflect_plugin.Ssrparser.wit_ssragens
  Ssreflect_plugin.Ssrparser.wit_ssrbinder
  Ssreflect_plugin.Ssrparser.wit_ssrbvar
  Ssreflect_plugin.Ssrparser.wit_ssrbwdview
  Ssreflect_plugin.Ssrparser.wit_ssrclausehyps
  Ssreflect_plugin.Ssrparser.wit_ssrclear
  Ssreflect_plugin.Ssrparser.wit_ssrclear_ne
  Ssreflect_plugin.Ssrparser.wit_ssrclseq
  Ssreflect_plugin.Ssrparser.wit_ssrcofixfwd
  Ssreflect_plugin.Ssrparser.wit_ssrcongrarg
  Ssreflect_plugin.Ssrparser.wit_ssrcpat
  Ssreflect_plugin.Ssrparser.wit_ssrdgens
  Ssreflect_plugin.Ssrparser.wit_ssrdgens_tl
  Ssreflect_plugin.Ssrparser.wit_ssrdir
  Ssreflect_plugin.Ssrparser.wit_ssrdoarg
  Ssreflect_plugin.Ssrparser.wit_ssrdocc
  Ssreflect_plugin.Ssrparser.wit_ssreqid
  Ssreflect_plugin.Ssrparser.wit_ssrexactarg
  Ssreflect_plugin.Ssrparser.wit_ssrfixfwd
  Ssreflect_plugin.Ssrparser.wit_ssrfwd
  Ssreflect_plugin.Ssrparser.wit_ssrfwdfmt
  Ssreflect_plugin.Ssrparser.wit_ssrfwdid
  Ssreflect_plugin.Ssrparser.wit_ssrfwdview
  Ssreflect_plugin.Ssrparser.wit_ssrgen
  Ssreflect_plugin.Ssrparser.wit_ssrhavefwd
  Ssreflect_plugin.Ssrparser.wit_ssrhint
  Ssreflect_plugin.Ssrparser.wit_ssrhoi_hyp
  Ssreflect_plugin.Ssrparser.wit_ssrhoi_id
  Ssreflect_plugin.Ssrparser.wit_ssrhpats
  Ssreflect_plugin.Ssrparser.wit_ssrhpats_nobs
  Ssreflect_plugin.Ssrparser.wit_ssrhpats_wtransp
  Ssreflect_plugin.Ssrparser.wit_ssrhyp
  Ssreflect_plugin.Ssrparser.wit_ssrhoi_hyp
  Ssreflect_plugin.Ssrparser.wit_ssrhoi_id
  Ssreflect_plugin.Ssrparser.wit_ssrhoirep
  Ssreflect_plugin.Ssrparser.wit_ssrindex
  Ssreflect_plugin.Ssrparser.wit_ssrintros
  Ssreflect_plugin.Ssrparser.wit_ssrintros_ne
  Ssreflect_plugin.Ssrparser.wit_ssrintrosarg
  Ssreflect_plugin.Ssrparser.wit_ssriorpat
  Ssreflect_plugin.Ssrparser.wit_ssripat
  Ssreflect_plugin.Ssrparser.wit_ssripatrep
  Ssreflect_plugin.Ssrparser.wit_ssripats_ne
  Ssreflect_plugin.Ssrparser.wit_ssripats

  Ssreflect_plugin.Ssrparser.wit_ssrmmod
  Ssreflect_plugin.Ssrparser.wit_ssrmult
  Ssreflect_plugin.Ssrparser.wit_ssrmult_ne

  Ssreflect_plugin.Ssrparser.wit_ssrocc
  Ssreflect_plugin.Ssrparser.wit_ssrortacarg
  Ssreflect_plugin.Ssrparser.wit_ssrortacs
  Ssreflect_plugin.Ssrparser.wit_ssrpattern_squarep
  Ssreflect_plugin.Ssrparser.wit_ssrpattern_ne_squarep

  Ssreflect_plugin.Ssrparser.wit_ssrposefwd
  Ssreflect_plugin.Ssrparser.wit_ssrrpat
  Ssreflect_plugin.Ssrparser.wit_ssrrule
  Ssreflect_plugin.Ssrparser.wit_ssrrule_ne
  Ssreflect_plugin.Ssrparser.wit_ssrrwarg

  Ssreflect_plugin.Ssrparser.wit_ssrrwkind
  Ssreflect_plugin.Ssrparser.wit_ssrrwocc

  Ssreflect_plugin.Ssrparser.wit_ssrseqarg
  Ssreflect_plugin.Ssrparser.wit_ssrseqdir
  Ssreflect_plugin.Ssrparser.wit_ssrsetfwd
  Ssreflect_plugin.Ssrparser.wit_ssrsimpl
  Ssreflect_plugin.Ssrparser.wit_ssrsimpl_ne
  Ssreflect_plugin.Ssrparser.wit_ssrsimplrep
  Ssreflect_plugin.Ssrparser.wit_ssrstruct
  Ssreflect_plugin.Ssrparser.wit_ssrsufffwd

  Ssreflect_plugin.Ssrparser.wit_ssrtacarg
  Ssreflect_plugin.Ssrparser.wit_ssrtclarg
  Ssreflect_plugin.Ssrparser.wit_ssrterm

  Ssreflect_plugin.Ssrparser.wit_ssrunlockarg
  Ssreflect_plugin.Ssrparser.wit_ssrunlockargs

  Ssreflect_plugin.Ssrparser.wit_ssrwgen
  Ssreflect_plugin.Ssrparser.wit_ssrwlogfwd
*)
  ()

let _ = register ()
