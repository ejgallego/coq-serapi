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
  [%import: Ssreflect_plugin.Ssrast.ssrhyp]
  [@@deriving sexp]

type ssrhyp_or_id =
  [%import: Ssreflect_plugin.Ssrast.ssrhyp_or_id]
  [@@deriving sexp]

type ssrhyps =
  [%import: Ssreflect_plugin.Ssrast.ssrhyps]
  [@@deriving sexp]

type ssrdir =
  [%import: Ssreflect_plugin.Ssrast.ssrdir]
  [@@deriving sexp]

type ssrsimpl =
  [%import: Ssreflect_plugin.Ssrast.ssrsimpl]
  [@@deriving sexp]

type ssrmmod =
  [%import: Ssreflect_plugin.Ssrast.ssrmmod]
  [@@deriving sexp]

type ssrmult =
  [%import: Ssreflect_plugin.Ssrast.ssrmult]
  [@@deriving sexp]

type ssrocc =
  [%import: Ssreflect_plugin.Ssrast.ssrocc]
  [@@deriving sexp]

type ssrindex =
  [%import: Ssreflect_plugin.Ssrast.ssrindex]
  [@@deriving sexp]

type ssrclear =
  [%import: Ssreflect_plugin.Ssrast.ssrclear]
  [@@deriving sexp]

type ssrdocc =
  [%import: Ssreflect_plugin.Ssrast.ssrdocc]
  [@@deriving sexp]

type ssrtermkind =
  [%import: Ssreflect_plugin.Ssrast.ssrtermkind]
  [@@deriving sexp]

type ssrterm =
  [%import: Ssreflect_plugin.Ssrast.ssrterm]
  [@@deriving sexp]

type ast_closure_term =
  [%import: Ssreflect_plugin.Ssrast.ast_closure_term]
  [@@deriving sexp]

type ssrview =
  [%import: Ssreflect_plugin.Ssrast.ssrview]
  [@@deriving sexp]

type anon_kind =
  [%import: Ssreflect_plugin.Ssrast.anon_kind]
  [@@deriving sexp]

(* type anon_iter =
 *   [%import: Ssreflect_plugin.Ssrast.anon_iter]
 *   [@@deriving sexp] *)

type id_block =
  [%import: Ssreflect_plugin.Ssrast.id_block]
  [@@deriving sexp]

type ssripat =
  [%import: Ssreflect_plugin.Ssrast.ssripat]
  [@@deriving sexp]
and ssripats =
  [%import: Ssreflect_plugin.Ssrast.ssripats]
  [@@deriving sexp]
and ssripatss =
  [%import: Ssreflect_plugin.Ssrast.ssripatss]
  [@@deriving sexp]
and ssripatss_or_block =
  [%import: Ssreflect_plugin.Ssrast.ssripatss_or_block]
  [@@deriving sexp]

type ssrhpats =
  [%import: Ssreflect_plugin.Ssrast.ssrhpats]
  [@@deriving sexp]

type ssrhpats_wtransp =
  [%import: Ssreflect_plugin.Ssrast.ssrhpats_wtransp]
  [@@deriving sexp]

type ssrintrosarg =
  [%import: Ssreflect_plugin.Ssrast.ssrintrosarg]
  [@@deriving sexp]

type ssrfwdid =
  [%import: Ssreflect_plugin.Ssrast.ssrfwdid]
  [@@deriving sexp]

type 'term ssrbind =
  [%import: 'term Ssreflect_plugin.Ssrast.ssrbind]
  [@@deriving sexp]

type ssrbindfmt =
  [%import: Ssreflect_plugin.Ssrast.ssrbindfmt]
  [@@deriving sexp]

type 'term ssrbindval =
  [%import: 'term Ssreflect_plugin.Ssrast.ssrbindval]
  [@@deriving sexp]

type ssrfwdkind =
  [%import: Ssreflect_plugin.Ssrast.ssrfwdkind]
  [@@deriving sexp]

type ssrfwdfmt =
  [%import: Ssreflect_plugin.Ssrast.ssrfwdfmt]
  [@@deriving sexp]

type ssrclseq =
  [%import: Ssreflect_plugin.Ssrast.ssrclseq]
  [@@deriving sexp]

type 'tac ssrhint =
  [%import: 'tac Ssreflect_plugin.Ssrast.ssrhint]
  [@@deriving sexp]

type 'tac fwdbinders =
  [%import: 'tac Ssreflect_plugin.Ssrast.fwdbinders]
  [@@deriving sexp]

type 'tac ffwbinders =
  [%import: 'tac Ssreflect_plugin.Ssrast.ffwbinders]
  [@@deriving sexp]

type clause =
  [%import: Ssreflect_plugin.Ssrast.clause]
  [@@deriving sexp]

type clauses =
  [%import: Ssreflect_plugin.Ssrast.clauses]
  [@@deriving sexp]

type wgen =
  [%import: Ssreflect_plugin.Ssrast.wgen]
  [@@deriving sexp]

type 'a ssrdoarg =
  [%import: 'a Ssreflect_plugin.Ssrast.ssrdoarg]
  [@@deriving sexp]

type 'a ssrseqarg =
  [%import: 'a Ssreflect_plugin.Ssrast.ssrseqarg]
  [@@deriving sexp]

type 'a ssragens =
  [%import: 'a Ssreflect_plugin.Ssrast.ssragens]
  [@@deriving sexp]

type ssrapplyarg =
  [%import: Ssreflect_plugin.Ssrast.ssrapplyarg]
  [@@deriving sexp]

type 'a ssrcasearg =
  [%import: 'a Ssreflect_plugin.Ssrast.ssrcasearg]
  [@@deriving sexp]

type 'a ssrmovearg =
  [%import: 'a Ssreflect_plugin.Ssrast.ssrmovearg]
  [@@deriving sexp]
