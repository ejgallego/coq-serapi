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

open Genarg

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

type 'a generic_argument = 'a Genarg.generic_argument

let generic_argument_of_sexp _ _x = Obj.magic 0


let rec sexp_of_genarg_type : type a b c. string -> (a, b, c) genarg_type -> t = fun lvl gt ->
  match gt with
  | ExtraArg tag   -> List [Atom "ExtraArg"; Atom lvl; Atom (ArgT.repr tag)]
  | ListArg rt     -> List [Atom "ListArg"; sexp_of_genarg_type lvl rt]
  | OptArg  rt     -> List [Atom "OptArg";  sexp_of_genarg_type lvl rt]
  | PairArg(t1,t2) -> List [Atom "PairArg"; sexp_of_genarg_type lvl t1; sexp_of_genarg_type lvl t2]

let sexp_of_genarg_type : type a. a generic_argument -> t =
  fun g -> match g with
  | GenArg (aat, _) -> begin
      match aat with
      | Glbwit gt -> sexp_of_genarg_type "glb" gt
      | Topwit gt -> sexp_of_genarg_type "top" gt
      | Rawwit gt -> sexp_of_genarg_type "raw" gt
    end

(*
open Ltac_plugin
let sexp_of_constr_expr     = ref (fun _ -> Atom "constr_expr_hook")
let sexp_of_glob_expr       = ref (fun _ -> Atom "glob_expr_hook")
let sexp_of_constr          = ref (fun _ -> Atom "constr_hook")

let sexp_of_raw_tactic_expr  = ref (fun _ -> Atom "raw_tactic_expr_hook")
let sexp_of_glob_tactic_expr = ref (fun _ -> Atom "glob_tactic_expr_hook")
let sexp_of_tactic_val_t     = ref (fun _ -> Atom "tactic_val_t_hook")

let sexp_of_tacdef_body      = ref (fun _ -> Atom "tacdef_body_hook")
*)

(*
open Sexplib.Conv

(* This likely needs to be tweaked, but it is a start *)
type (_, _, _) ser_genarg_table_entry =
  Ser_tentry :
    ('a, 'b, 'c) genarg_type * ('a -> t) * ('b -> t) * ('c -> t) -> ('a, 'b, 'c) ser_genarg_table_entry

let _ser_wit_constr =
  Ser_tentry (Stdarg.wit_constr, !sexp_of_constr_expr, !sexp_of_glob_expr, !sexp_of_constr)

let _ser_wit_tactic =
  Ser_tentry (Tacarg.wit_tactic, !sexp_of_raw_tactic_expr, !sexp_of_glob_tactic_expr, !sexp_of_tactic_val_t)

let _ser_wit_opt fc = match fc with | Ser_tentry(f, fa, fb, fc) ->
  Ser_tentry (Genarg.wit_opt f, sexp_of_option fa, sexp_of_option fb, sexp_of_option fc)

let _ser_opt_tac = _ser_wit_opt _ser_wit_tactic
*)

(* let sexp_of_extraarg_gen (GenArg (Rawwit (ExtraArg _ as wit), x)) (Ser_tentry(wit_e,s1,s2,s3)) : t = *)
(*   match genarg_type_eq wit wit_e with *)
(*   | None   -> Atom "Unknown ExtraArg" *)
(*   | Some _ -> s1 x *)

(* XXX use register ***)

(* Needs more work, but getting there *)
(*
let sexp_of_extraarg g =
  (* XXX: Register mechanism needed *)
  if has_type g (rawwit Stdarg.wit_constr) then
    begin
      let g_out : Constrexpr.constr_expr = Genarg.out_gen (rawwit Stdarg.wit_constr) g in
      !sexp_of_constr_expr g_out
    end
  else if has_type g (rawwit Tacarg.wit_ltac) then
    begin
      let g_out : Tacexpr.raw_tactic_expr = Genarg.out_gen (rawwit Tacarg.wit_tactic) g in
      !sexp_of_raw_tactic_expr g_out
    end
  else if has_type g (rawwit G_ltac.wit_ltac_info) then
    begin
      let g_out : int = Genarg.out_gen (rawwit G_ltac.wit_ltac_info) g in
      Sexplib.Conv.sexp_of_int g_out
    end
  else if has_type g (rawwit G_ltac.wit_ltac_selector) then
    begin
      let g_out : Vernacexpr.goal_selector = Genarg.out_gen (rawwit G_ltac.wit_ltac_selector) g in
      !sexp_of_goal_selector g_out
    end
  else if has_type g (rawwit G_ltac.wit_ltac_use_default) then
    begin
      let g_out : bool = Genarg.out_gen (rawwit G_ltac.wit_ltac_use_default) g in
      sexp_of_bool g_out
    end
  else if has_type g (rawwit G_ltac.wit_ltac_tacdef_body) then
    begin
      let g_out : Tacexpr.tacdef_body = Genarg.out_gen (rawwit G_ltac.wit_ltac_tacdef_body) g in
      !sexp_of_tacdef_body g_out
    end
  else if has_type g (rawwit Tacarg.wit_tactic) then
    begin
      let g_out : Tacexpr.raw_tactic_expr = Genarg.out_gen (rawwit Tacarg.wit_tactic) g in
      !sexp_of_raw_tactic_expr g_out
    end
  else Atom (Pp.string_of_ppcmds (pr_argument_type (genarg_tag g)))

let rec sexp_of_rawgen (GenArg (Rawwit wit, x) as g) =
  let ucc wit m = sexp_of_rawgen (in_gen (rawwit wit) m) in
  match wit with
  | PairArg (w1, w2) -> sexp_of_pair   (ucc w1) (ucc w2) x
  | ListArg wit      -> sexp_of_list   (ucc wit) x
  | OptArg wit       -> sexp_of_option (ucc wit) x
  | ExtraArg _       -> sexp_of_extraarg g
*)

(* We need to generalize this to use the proper printers for opt *)
let sexp_of_genarg_val : type a. a generic_argument -> t =
  fun g -> match g with
  | GenArg (aat, _x) -> begin
    match aat with
    | Glbwit _gt -> Atom "XXX Global GenARG"
    | Topwit _gt -> Atom "XXX Typed GenARG"
    | Rawwit _gt -> Atom "XXX Raw GenARG"
    (* | Rawwit _gt -> sexp_of_rawgen g *)
  end

let sexp_of_generic_argument : type a. (a -> t) -> a Genarg.generic_argument -> t = fun _ g ->
  (* let gtype = sexp_of_genarg_type g in *)
  let _ = sexp_of_genarg_type in
  let gval  = sexp_of_genarg_val  g in
  (* List [List [Atom "GenArgType"; gtype]; List [Atom "GenArgVal"; gval]] *)
  gval

type glob_generic_argument = [%import: Genarg.glob_generic_argument]
  [@@deriving sexp]

type raw_generic_argument  = [%import: Genarg.raw_generic_argument]
  [@@deriving sexp]

type typed_generic_argument  = [%import: Genarg.typed_generic_argument]
  [@@deriving sexp]

