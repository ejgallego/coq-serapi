(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type 'a red_atom = 'a Genredexpr.red_atom

val red_atom_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a red_atom
val sexp_of_red_atom : ('a -> Sexp.t) -> 'a red_atom -> Sexp.t

type 'a glob_red_flag =  'a Genredexpr.glob_red_flag

val glob_red_flag_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a glob_red_flag
val sexp_of_glob_red_flag : ('a -> Sexp.t) -> 'a glob_red_flag -> Sexp.t
val glob_red_flag_of_yojson : (Yojson.Safe.t -> ('a, string) Result.result) -> Yojson.Safe.t -> ('a glob_red_flag, string) Result.result
val glob_red_flag_to_yojson : ('a -> Yojson.Safe.t) -> 'a glob_red_flag -> Yojson.Safe.t

type ('a, 'b, 'c) red_expr_gen =  ('a, 'b, 'c) Genredexpr.red_expr_gen

val red_expr_gen_of_sexp :
  (Sexp.t -> 'a) ->
  (Sexp.t -> 'b) ->
  (Sexp.t -> 'c) -> Sexp.t -> ('a, 'b, 'c) red_expr_gen
val sexp_of_red_expr_gen :
  ('a -> Sexp.t) ->
  ('b -> Sexp.t) ->
  ('c -> Sexp.t) -> ('a, 'b, 'c) red_expr_gen -> Sexp.t

type ('a, 'b, 'c) may_eval =  ('a, 'b, 'c) Genredexpr.may_eval
val may_eval_of_sexp :
  (Sexp.t -> 'a) ->
  (Sexp.t -> 'b) ->
  (Sexp.t -> 'c) -> Sexp.t -> ('a, 'b, 'c) may_eval
val sexp_of_may_eval :
  ('a -> Sexp.t) ->
  ('b -> Sexp.t) ->
  ('c -> Sexp.t) -> ('a, 'b, 'c) may_eval -> Sexp.t

type raw_red_expr = Genredexpr.raw_red_expr [@@deriving sexp,yojson,hash,compare]

type r_cst = Genredexpr.r_cst
val r_cst_of_sexp : Sexp.t -> r_cst
val sexp_of_r_cst : r_cst -> Sexp.t
val r_cst_of_yojson : Yojson.Safe.t -> (r_cst, string) Result.result
val r_cst_to_yojson : r_cst -> Yojson.Safe.t

type r_trm = Genredexpr.r_trm
val r_trm_of_sexp : Sexp.t -> r_trm
val sexp_of_r_trm : r_trm -> Sexp.t
val r_trm_of_yojson : Yojson.Safe.t -> (r_trm, string) Result.result
val r_trm_to_yojson : r_trm -> Yojson.Safe.t

type r_pat = Genredexpr.r_pat
val r_pat_of_sexp : Sexp.t -> r_pat
val sexp_of_r_pat : r_pat -> Sexp.t
val r_pat_of_yojson : Yojson.Safe.t -> (r_pat, string) Result.result
val r_pat_to_yojson : r_pat -> Yojson.Safe.t

type 'a and_short_name = 'a Genredexpr.and_short_name
val and_short_name_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a and_short_name
val sexp_of_and_short_name : ('a -> Sexp.t) -> 'a and_short_name -> Sexp.t
