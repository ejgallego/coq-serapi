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

open Sexplib.Sexp

(**********************************************************************)
(* GenArg                                                             *)
(**********************************************************************)

type rlevel = [%import: Genarg.rlevel]
type glevel = [%import: Genarg.glevel]
type tlevel = [%import: Genarg.tlevel]

let rlevel_of_sexp _ = Obj.magic 0
let sexp_of_rlevel _ = Atom "GA_rlevel"

let glevel_of_sexp _ = Obj.magic 0
let sexp_of_glevel _ = Atom "GA_glevel"

let tlevel_of_sexp _ = Obj.magic 0
let sexp_of_tlevel _ = Atom "GA_tlevel"

(* type ('a, 'b) abstract_argument_type = *)
(*   ('a, 'b) Genarg.abstract_argument_type *)
  (* [%import: ('a, 'b) Genarg.abstract_argument_type *)
  (* ] *)

type 'a generic_argument =
  'a Genarg.generic_argument

let generic_argument_of_sexp _ _x = Obj.magic 0

open Genarg

(*   if has_type (rawwit Stdarg.wit_constr) g then *)
(*     let a = Genarg.out_gen g (topwit Stdarg.wit_constr) in *)

let rec sexp_of_genarg_type : type a b c. string -> (a, b, c) genarg_type -> t = fun lvl gt ->
  match gt with
  | ExtraArg tag   -> List [Atom "ExtraArg"; Atom lvl; Atom (ArgT.repr tag)]
  | ListArg rt     -> List [Atom "ListArg"; sexp_of_genarg_type lvl rt]
  | OptArg  rt     -> List [Atom "OptArg";  sexp_of_genarg_type lvl rt]
  | PairArg(t1,t2) -> List [Atom "PairArg"; sexp_of_genarg_type lvl t1; sexp_of_genarg_type lvl t2]

let sexp_of_generic_argument : type a. (a -> t) -> a Genarg.generic_argument -> t =
  fun _ g ->
  match g with
  | GenArg (aat, _ax) -> begin
      match aat with
      | Glbwit gt -> sexp_of_genarg_type "glb" gt
      | Topwit gt -> sexp_of_genarg_type "top" gt
      | Rawwit gt -> sexp_of_genarg_type "raw" gt
    end

type glob_generic_argument = [%import: Genarg.glob_generic_argument]
  [@@deriving sexp]

type raw_generic_argument  = [%import: Genarg.raw_generic_argument]
  [@@deriving sexp]

type typed_generic_argument  = [%import: Genarg.typed_generic_argument]
  [@@deriving sexp]

