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
  [%import: Ssreflect_plugin.Ssrparser.ssrfwdview]
  [@@deriving sexp]

type ssreqid =
  [%import: Ssreflect_plugin.Ssrparser.ssreqid]
  [@@deriving sexp]

type ssrarg =
  [%import: Ssreflect_plugin.Ssrparser.ssrarg]
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

module A1 = struct
  type h1 = Ser_tacexpr.raw_tactic_expr ssrseqarg
  [@@deriving sexp]
  type h2 = Ser_tacexpr.glob_tactic_expr ssrseqarg
  [@@deriving sexp]
  type h3 = Geninterp.Val.t ssrseqarg
  [@@deriving sexp]
end

let ser_wit_ssrseqarg = let open A1 in Ser_genarg.
  { raw_ser = sexp_of_h1
  ; raw_des = h1_of_sexp

  ; glb_ser = sexp_of_h2
  ; glb_des = h2_of_sexp

  ; top_ser = sexp_of_h3
  ; top_des = h3_of_sexp
  }

module A2 = struct
  type h1 = Ser_tacexpr.raw_tactic_expr * ssripats
  [@@deriving sexp]
  type h2 = Ser_tacexpr.glob_tactic_expr * ssripats
  [@@deriving sexp]
  type h3 = Geninterp.Val.t * ssripats
  [@@deriving sexp]
end

let ser_wit_ssrintrosarg = let open A2 in Ser_genarg.
  { raw_ser = sexp_of_h1
  ; raw_des = h1_of_sexp

  ; glb_ser = sexp_of_h2
  ; glb_des = h2_of_sexp

  ; top_ser = sexp_of_h3
  ; top_des = h3_of_sexp
  }

module A3 = struct
  type h1 = Ser_tacexpr.raw_tactic_expr ffwbinders
  [@@deriving sexp]
  type h2 = Ser_tacexpr.glob_tactic_expr ffwbinders
  [@@deriving sexp]
  type h3 = Geninterp.Val.t ffwbinders
  [@@deriving sexp]
end

let ser_wit_ssrsufffwd = let open A3 in Ser_genarg.
  { raw_ser = sexp_of_h1 ; raw_des = h1_of_sexp ; glb_ser = sexp_of_h2
  ; glb_des = h2_of_sexp ; top_ser = sexp_of_h3 ; top_des = h3_of_sexp
  }

module A4 = struct
  type h1 = ((int * Ssreflect_plugin.Ssrast.ssrterm) * Ssrmatching_plugin.Ssrmatching.cpattern ssragens)
  [@@deriving sexp]
end

let ser_wit_ssrcongrarg = let open A4 in Ser_genarg.mk_uniform sexp_of_h1 h1_of_sexp

module A5 = struct
  type h1 = Ser_tacexpr.raw_tactic_expr ssrdoarg
  [@@deriving sexp]
  type h2 = Ser_tacexpr.glob_tactic_expr ssrdoarg
  [@@deriving sexp]
  type h3 = Geninterp.Val.t ssrdoarg
  [@@deriving sexp]

end

let ser_wit_ssrdoarg = let open A5 in Ser_genarg.
  { raw_ser = sexp_of_h1 ; raw_des = h1_of_sexp ; glb_ser = sexp_of_h2
  ; glb_des = h2_of_sexp ; top_ser = sexp_of_h3 ; top_des = h3_of_sexp
  }

module A6 = struct
  type h1 = ((ssrfwdfmt * (cpattern * ast_closure_term option)) * ssrdocc)
  [@@deriving sexp]
end

let ser_wit_ssrsetfwd = let open A6 in Ser_genarg.mk_uniform sexp_of_h1 h1_of_sexp

module A7 = struct
  type h1 = Ser_tacexpr.raw_tactic_expr ssrhint
  [@@deriving sexp]
  type h2 = Ser_tacexpr.glob_tactic_expr ssrhint
  [@@deriving sexp]
  type h3 = Geninterp.Val.t ssrhint
  [@@deriving sexp]
end

let ser_wit_ssrhint = let open A7 in Ser_genarg.
  { raw_ser = sexp_of_h1 ; raw_des = h1_of_sexp ; glb_ser = sexp_of_h2
  ; glb_des = h2_of_sexp ; top_ser = sexp_of_h3 ; top_des = h3_of_sexp
  }

module A8 = struct
  type h1 = ssrfwdfmt * ast_closure_term
  [@@deriving sexp]
end

let ser_wit_ssrposefwd = let open A8 in Ser_genarg.mk_uniform sexp_of_h1 h1_of_sexp

module A9 = struct
  type h1 = ssrocc * ssrterm
  [@@deriving sexp]
end

let ser_wit_ssrunlockarg = let open A9 in Ser_genarg.mk_uniform sexp_of_h1 h1_of_sexp

module A10 = struct
  type h1 = clause list * (ssrfwdfmt * ast_closure_term)
  [@@deriving sexp]
end

let ser_wit_ssrwlogfwd = let open A10 in Ser_genarg.mk_uniform sexp_of_h1 h1_of_sexp

module A11 = struct
  type h1 = Names.Id.t * (ssrfwdfmt * ast_closure_term)
  [@@deriving sexp]
end

let ser_wit_ssrfixfwd = let open A11 in Ser_genarg.mk_uniform sexp_of_h1 h1_of_sexp

module A12 = struct
  type h1 = ssrfwdfmt * ast_closure_term
  [@@deriving sexp]
end

let ser_wit_ssrfwd = let open A12 in Ser_genarg.mk_uniform sexp_of_h1 h1_of_sexp

let register () =
  let open Ser_genarg in
  let open Ssreflect_plugin.Ssrparser in

  register_genser wit_ssrapplyarg        ser_wit_ssrapplyarg;
  register_genser wit_ssrarg             ser_wit_ssrarg;
  register_genser wit_ssrcasearg         ser_wit_ssrmovearg;
  register_genser wit_ssrclauses         ser_wit_clauses;
  register_genser wit_ssrmovearg         ser_wit_ssrmovearg;
  register_genser wit_ssrhavefwdwbinders ser_wit_ssrhavefwdwbinders;
  register_genser wit_ssrhintarg         ser_wit_ssrhintarg;
  register_genser wit_ssrrwargs          ser_wit_ssrrwargs;

  (* register_genser wit_ast_closure_lterm ser_wit_ast_closure_lterm
     register_genser wit_ast_closure_term  ser_wit_ast_closure_term
     register_genser wit_ssr_idcomma       ser_wit_ssr_idcomma
     register_genser wit_ssragen           ser_wit_ssragen
     register_genser wit_ssragens          ser_wit_ssragens
     register_genser wit_ssrbinder         ser_wit_ssrbinder
     register_genser wit_ssrbvar           ser_wit_ssrbvar
     register_genser wit_ssrbwdview        ser_wit_ssrbwdview
     register_genser wit_ssrclausehyps     ser_wit_ssrclausehyps
     register_genser wit_ssrclear          ser_wit_ssrclear
     register_genser wit_ssrclear_ne       ser_wit_ssrclear_ne
     register_genser wit_ssrclseq          ser_wit_ssrclseq
     register_genser wit_ssrcofixfwd       ser_wit_ssrcofixfwd *)

  register_genser wit_ssrcongrarg ser_wit_ssrcongrarg;
  register_genser wit_ssrcpat     (mk_uniform sexp_of_ssripat ssripat_of_sexp);
  register_genser wit_ssrdgens    (mk_uniform (sexp_of_ssragens sexp_of_cpattern) (ssragens_of_sexp cpattern_of_sexp));
  register_genser wit_ssrdgens_tl (mk_uniform (sexp_of_ssragens sexp_of_cpattern) (ssragens_of_sexp cpattern_of_sexp));
  register_genser wit_ssrdir      (mk_uniform sexp_of_ssrdir ssrdir_of_sexp);
  register_genser wit_ssrdoarg    ser_wit_ssrdoarg;
(*
  Ssreflect_plugin.Ssrparser.wit_ssrdocc
  Ssreflect_plugin.Ssrparser.wit_ssreqid
*)
  register_genser wit_ssrexactarg ser_wit_ssrapplyarg;
  register_genser wit_ssrfixfwd   ser_wit_ssrfixfwd;
  register_genser wit_ssrfwd      ser_wit_ssrfwd;
  register_genser wit_ssrfwdfmt   (mk_uniform sexp_of_ssrfwdfmt ssrfwdfmt_of_sexp);
  register_genser wit_ssrfwdid    Ser_names.(mk_uniform Id.sexp_of_t Id.t_of_sexp);

(*
  Ssreflect_plugin.Ssrparser.wit_ssrfwdview
  Ssreflect_plugin.Ssrparser.wit_ssrgen
  Ssreflect_plugin.Ssrparser.wit_ssrhavefwd
*)
  register_genser wit_ssrhint ser_wit_ssrhint;
(*
  Ssreflect_plugin.Ssrparser.wit_ssrhoi_hyp
  Ssreflect_plugin.Ssrparser.wit_ssrhoi_id
*)
  register_genser wit_ssrhpats         (mk_uniform sexp_of_ssrhpats ssrhpats_of_sexp);
  register_genser wit_ssrhpats_nobs    (mk_uniform sexp_of_ssrhpats ssrhpats_of_sexp);
  register_genser wit_ssrhpats_wtransp (mk_uniform sexp_of_ssrhpats_wtransp ssrhpats_wtransp_of_sexp);

(*
  Ssreflect_plugin.Ssrparser.wit_ssrhyp
  Ssreflect_plugin.Ssrparser.wit_ssrhoi_hyp
  Ssreflect_plugin.Ssrparser.wit_ssrhoi_id
  Ssreflect_plugin.Ssrparser.wit_ssrhoirep
  Ssreflect_plugin.Ssrparser.wit_ssrindex
  Ssreflect_plugin.Ssrparser.wit_ssrintros
  Ssreflect_plugin.Ssrparser.wit_ssrintros_ne
*)
  register_genser wit_ssrintrosarg ser_wit_ssrintrosarg;
(*
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
*)
  register_genser wit_ssrposefwd ser_wit_ssrposefwd;
  register_genser wit_ssrrpat    (mk_uniform sexp_of_ssripat ssripat_of_sexp);

(*
  Ssreflect_plugin.Ssrparser.wit_ssrrule
  Ssreflect_plugin.Ssrparser.wit_ssrrule_ne
  Ssreflect_plugin.Ssrparser.wit_ssrrwarg

  Ssreflect_plugin.Ssrparser.wit_ssrrwkind
  Ssreflect_plugin.Ssrparser.wit_ssrrwocc
  *)

  register_genser wit_ssrseqarg ser_wit_ssrseqarg;
  register_genser wit_ssrseqdir (mk_uniform sexp_of_ssrdir ssrdir_of_sexp);
  register_genser wit_ssrsetfwd ser_wit_ssrsetfwd;
(*
  Ssreflect_plugin.Ssrparser.wit_ssrsimpl
  Ssreflect_plugin.Ssrparser.wit_ssrsimpl_ne
  Ssreflect_plugin.Ssrparser.wit_ssrsimplrep
  Ssreflect_plugin.Ssrparser.wit_ssrstruct
*)
  register_genser wit_ssrsufffwd ser_wit_ssrsufffwd;
  register_genser wit_ssrtacarg Ser_tacarg.ser_wit_tactic;
  register_genser wit_ssrtclarg Ser_tacarg.ser_wit_tactic;

  register_genser wit_ssrterm       (mk_uniform sexp_of_ssrterm ssrterm_of_sexp);
  register_genser wit_ssrunlockarg  ser_wit_ssrunlockarg;
  register_genser wit_ssrunlockargs (gen_ser_list ser_wit_ssrunlockarg);
  register_genser wit_ssrwgen       (mk_uniform sexp_of_clause clause_of_sexp);
  register_genser wit_ssrwlogfwd    ser_wit_ssrwlogfwd;
  ()

let _ = register ()
