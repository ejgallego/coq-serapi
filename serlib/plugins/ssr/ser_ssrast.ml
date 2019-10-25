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
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Serlib

module Loc        = Ser_loc
module Names      = Ser_names
module Locus      = Ser_locus
module Constrexpr = Ser_constrexpr
module Genintern  = Ser_genintern
module Geninterp  = Ser_geninterp

module Ssrmatching_plugin = struct
  module Ssrmatching = Ser_ssrmatching
end

module Ltac_plugin = struct
  module Tacexpr = Ser_tacexpr
end

(* What a hack is ssreflect using... *)
module Proofview = struct
  type 'a tactic = 'a Proofview.tactic
  let tactic_of_sexp _ = Serlib_base.opaque_of_sexp ~typ:"Ssrast.tactic"
  let sexp_of_tactic _ = Serlib_base.sexp_of_opaque ~typ:"Ssrast.tactic"
end

type ssrhyp =
  [%import: Wrap_ssrast.ssrhyp]
  [@@deriving sexp]

type ssrhyp_or_id =
  [%import: Wrap_ssrast.ssrhyp_or_id]
  [@@deriving sexp]

type ssrhyps =
  [%import: Wrap_ssrast.ssrhyps]
  [@@deriving sexp]

type ssrdir =
  [%import: Wrap_ssrast.ssrdir]
  [@@deriving sexp]

type ssrsimpl =
  [%import: Wrap_ssrast.ssrsimpl]
  [@@deriving sexp]

type ssrmmod =
  [%import: Wrap_ssrast.ssrmmod]
  [@@deriving sexp]

type ssrmult =
  [%import: Wrap_ssrast.ssrmult]
  [@@deriving sexp]

type ssrocc =
  [%import: Wrap_ssrast.ssrocc]
  [@@deriving sexp]

type ssrindex =
  [%import: Wrap_ssrast.ssrindex]
  [@@deriving sexp]

type ssrclear =
  [%import: Wrap_ssrast.ssrclear]
  [@@deriving sexp]

type ssrdocc =
  [%import: Wrap_ssrast.ssrdocc]
  [@@deriving sexp]

type ssrtermkind =
  [%import: Wrap_ssrast.ssrtermkind]
  [@@deriving sexp]

type ssrterm =
  [%import: Wrap_ssrast.ssrterm]
  [@@deriving sexp]

type ast_closure_term =
  [%import: Wrap_ssrast.ast_closure_term]
  [@@deriving sexp]

type ssrview =
  [%import: Wrap_ssrast.ssrview]
  [@@deriving sexp]

type anon_kind =
  [%import: Wrap_ssrast.anon_kind]
  [@@deriving sexp]

(* type anon_iter =
 *   [%import: Wrap_ssrast.anon_iter]
 *   [@@deriving sexp] *)

type id_block =
  [%import: Wrap_ssrast.id_block]
  [@@deriving sexp]

type ssripat =
  [%import: Wrap_ssrast.ssripat]
  [@@deriving sexp]
and ssripats =
  [%import: Wrap_ssrast.ssripats]
  [@@deriving sexp]
and ssripatss =
  [%import: Wrap_ssrast.ssripatss]
  [@@deriving sexp]
and ssripatss_or_block =
  [%import: Wrap_ssrast.ssripatss_or_block]
  [@@deriving sexp]

type ssrhpats =
  [%import: Wrap_ssrast.ssrhpats]
  [@@deriving sexp]

type ssrhpats_wtransp =
  [%import: Wrap_ssrast.ssrhpats_wtransp]
  [@@deriving sexp]

type ssrintrosarg =
  [%import: Wrap_ssrast.ssrintrosarg]
  [@@deriving sexp]

type ssrfwdid =
  [%import: Wrap_ssrast.ssrfwdid]
  [@@deriving sexp]

type 'term ssrbind =
  [%import: 'term Wrap_ssrast.ssrbind]
  [@@deriving sexp]

type ssrbindfmt =
  [%import: Wrap_ssrast.ssrbindfmt]
  [@@deriving sexp]

type 'term ssrbindval =
  [%import: 'term Wrap_ssrast.ssrbindval]
  [@@deriving sexp]

type ssrfwdkind =
  [%import: Wrap_ssrast.ssrfwdkind]
  [@@deriving sexp]

type ssrfwdfmt =
  [%import: Wrap_ssrast.ssrfwdfmt]
  [@@deriving sexp]

type ssrclseq =
  [%import: Wrap_ssrast.ssrclseq]
  [@@deriving sexp]

type 'tac ssrhint =
  [%import: 'tac Wrap_ssrast.ssrhint]
  [@@deriving sexp]

type 'tac fwdbinders =
  [%import: 'tac Wrap_ssrast.fwdbinders]
  [@@deriving sexp]

type 'tac ffwbinders =
  [%import: 'tac Wrap_ssrast.ffwbinders]
  [@@deriving sexp]

type clause =
  [%import: Wrap_ssrast.clause]
  [@@deriving sexp]

type clauses =
  [%import: Wrap_ssrast.clauses]
  [@@deriving sexp]

type wgen =
  [%import: Wrap_ssrast.wgen]
  [@@deriving sexp]

type 'a ssrdoarg =
  [%import: 'a Wrap_ssrast.ssrdoarg]
  [@@deriving sexp]

type 'a ssrseqarg =
  [%import: 'a Wrap_ssrast.ssrseqarg]
  [@@deriving sexp]

type 'a ssragens =
  [%import: 'a Wrap_ssrast.ssragens]
  [@@deriving sexp]

type ssrapplyarg =
  [%import: Wrap_ssrast.ssrapplyarg]
  [@@deriving sexp]

type 'a ssrcasearg =
  [%import: 'a Wrap_ssrast.ssrcasearg]
  [@@deriving sexp]

type 'a ssrmovearg =
  [%import: 'a Wrap_ssrast.ssrmovearg]
  [@@deriving sexp]
