(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
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

let rlevel_of_sexp _ = `rlevel
let sexp_of_rlevel _ = Atom "GA_rlevel"

let glevel_of_sexp _ = `glevel
let sexp_of_glevel _ = Atom "GA_glevel"

let tlevel_of_sexp _ = `tlevel
let sexp_of_tlevel _ = Atom "GA_tlevel"

(* type ('a, 'b) abstract_argument_type = *)
(*   ('a, 'b) Genarg.abstract_argument_type *)
  (* [%import: ('a, 'b) Genarg.abstract_argument_type *)
  (* ] *)

type 'a generic_argument = 'a Genarg.generic_argument

let generic_argument_of_sexp _ _x =
  CErrors.user_err Pp.(str "SERAPI FIXME: cannot deserialize generic arguments yet")

let rec sexp_of_genarg_type : type a b c. string -> (a, b, c) genarg_type -> t = fun lvl gt ->
  match gt with
  | ExtraArg tag   -> List [Atom "ExtraArg"; Atom lvl; Atom (ArgT.repr tag)]
  | ListArg rt     -> List [Atom "ListArg"; sexp_of_genarg_type lvl rt]
  | OptArg  rt     -> List [Atom "OptArg";  sexp_of_genarg_type lvl rt]
  | PairArg(t1,t2) -> List [Atom "PairArg"; sexp_of_genarg_type lvl t1; sexp_of_genarg_type lvl t2]

type ('raw, 'glb, 'top) gen_ser =
  { raw_ser : 'raw -> Sexplib.Sexp.t;
    glb_ser : 'glb -> Sexplib.Sexp.t;
    top_ser : 'top -> Sexplib.Sexp.t;
  }

let gen_ser_list : ('raw, 'glb, 'top) gen_ser -> ('raw list, 'glb list, 'top list) gen_ser = fun g ->
  let open Sexplib.Conv in
  { raw_ser = sexp_of_list g.raw_ser;
    glb_ser = sexp_of_list g.glb_ser;
    top_ser = sexp_of_list g.top_ser;
  }

let gen_ser_opt : ('raw, 'glb, 'top) gen_ser -> ('raw option, 'glb option, 'top option) gen_ser = fun g ->
  let open Sexplib.Conv in
  { raw_ser = sexp_of_option g.raw_ser;
    glb_ser = sexp_of_option g.glb_ser;
    top_ser = sexp_of_option g.top_ser;
  }

let gen_ser_pair : ('raw1, 'glb1, 'top1) gen_ser -> ('raw2, 'glb2, 'top2) gen_ser ->
  (('raw1 * 'raw2), ('glb1 * 'glb2), ('top1 * 'top2)) gen_ser = fun g1 g2 ->
  let open Sexplib.Conv in
  { raw_ser = sexp_of_pair g1.raw_ser g2.raw_ser;
    glb_ser = sexp_of_pair g1.glb_ser g2.glb_ser;
    top_ser = sexp_of_pair g1.top_ser g2.top_ser;
  }

(* Generic printer *)
(* module SerObj : GenObj = struct *)
module SerObj = struct

  type ('raw, 'glb, 'top) obj = ('raw, 'glb, 'top) gen_ser

  let name = "ser_arg"
  let default ga =
    let open Sexplib in
    Some {
      raw_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; sexp_of_genarg_type "raw" ga]));
      glb_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; sexp_of_genarg_type "glb" ga]));
      top_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; sexp_of_genarg_type "top" ga]));
    }

end

module SerGen = Register(SerObj)

let register_genprint ty obj = SerGen.register0 ty obj

let rec get_gen_ser : type r g t. (r,g,t) Genarg.genarg_type -> (r,g,t) gen_ser =
  fun gt -> match gt with
  | Genarg.ExtraArg _      -> SerGen.obj gt
  | Genarg.ListArg  t      -> gen_ser_list (get_gen_ser t)
  | Genarg.OptArg   t      -> gen_ser_opt  (get_gen_ser t)
  | Genarg.PairArg(t1, t2) -> gen_ser_pair (get_gen_ser t1) (get_gen_ser t2)

(* We need to generalize this to use the proper printers for opt *)
let sexp_of_genarg_val : type a. a generic_argument -> t =
  fun g -> match g with
  | GenArg (g_ty, g_val) -> begin
      match g_ty with
      | Rawwit gt ->
        let pr = get_gen_ser gt in
        pr.raw_ser g_val
      | Glbwit gt ->
        let pr = get_gen_ser gt in
        pr.glb_ser g_val
      | Topwit gt ->
        let pr = get_gen_ser gt in
        pr.top_ser g_val
    end

let sexp_of_generic_argument : type a. (a -> t) -> a Genarg.generic_argument -> t =
  fun _level_tag g ->
  sexp_of_genarg_val g

type glob_generic_argument =
  [%import: Genarg.glob_generic_argument]
  [@@deriving sexp]

type raw_generic_argument =
  [%import: Genarg.raw_generic_argument]
  [@@deriving sexp]

type typed_generic_argument =
  [%import: Genarg.typed_generic_argument]
  [@@deriving sexp]

