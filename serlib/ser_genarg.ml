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

open Sexplib

(**********************************************************************)
(* GenArg                                                             *)
(**********************************************************************)

open Genarg

type rlevel =
  [%import: Genarg.rlevel]
  [@@deriving sexp]
type glevel =
  [%import: Genarg.glevel]
  [@@deriving sexp]
type tlevel =
  [%import: Genarg.tlevel]
  [@@deriving sexp]

open Sexp

(*
module ArgT = struct
  type ('a,'b,'c) tag = ('a,'b,'c) ArgT.tag
  let t_of_sexp x =
end
*)

let rec sexp_of_genarg_type : type a b c. (a, b, c) genarg_type -> t = fun gt ->
  match gt with
  | ExtraArg tag   -> List [Atom "ExtraArg"; Atom (ArgT.repr tag)]
  | ListArg rt     -> List [Atom "ListArg"; sexp_of_genarg_type rt]
  | OptArg  rt     -> List [Atom "OptArg";  sexp_of_genarg_type rt]
  | PairArg(t1,t2) -> List [Atom "PairArg"; sexp_of_genarg_type t1; sexp_of_genarg_type t2]

(* let sexp_of_argument_type *)
let rec argument_type_of_sexp : t -> argument_type = fun sexp ->
  match sexp with
  | List [Atom "ExtraArg"; Atom tag] ->
    begin match ArgT.name tag with
      | None              -> raise (Failure "SEXP Exception")
      | Some (ArgT.Any t) -> ArgumentType (ExtraArg t)
    end
  | List [Atom "ListArg"; s1] ->
    let (ArgumentType t) = argument_type_of_sexp s1 in
    ArgumentType (ListArg t)
  | List [Atom "OptArg";  s1] ->
    let (ArgumentType t) = argument_type_of_sexp s1 in
    ArgumentType (OptArg t)
  | List [Atom "PairArg"; s1; s2] ->
    let (ArgumentType t1) = argument_type_of_sexp s1 in
    let (ArgumentType t2) = argument_type_of_sexp s2 in
    ArgumentType (PairArg(t1,t2))
  | _ -> raise (Failure "SEXP Exception")

let sexp_of_abstract_argument_type : type lvl. ('o, lvl) abstract_argument_type -> t * t = fun  at ->
  match at with
  | Rawwit w -> Atom "raw", sexp_of_genarg_type w
  | Glbwit w -> Atom "glb", sexp_of_genarg_type w
  | Topwit w -> Atom "top", sexp_of_genarg_type w

type gen_abstype = GenTyp : ('a, 'l) abstract_argument_type -> gen_abstype

let abstype_of_sexp : t -> gen_abstype = fun s ->
  match s with
  | List [Atom "raw"; sty] ->
    let (ArgumentType ty) = argument_type_of_sexp sty in
    GenTyp (Rawwit ty)
  | List [Atom "glb"; sty] ->
    let (ArgumentType ty) = argument_type_of_sexp sty in
    GenTyp (Glbwit ty)
  | List [Atom "top"; sty] ->
    let (ArgumentType ty) = argument_type_of_sexp sty in
    GenTyp (Topwit ty)
  | _ -> raise Not_found

let split_gensexp s =
  match s with
  | List [Atom "GenArg"; sty; sobj] -> sty, sobj
  | _ -> raise (Failure "ERROR")

(* for warnings *)
let _ = abstype_of_sexp
let _ = split_gensexp
(*
let generic_argument_of_sexp : type a. t -> a generic_argument = fun sexp ->
  let s_ty, s_obj = split_gensexp sexp in
  let (GenTyp aat) = abstype_of_sexp s_ty in
  let obj = Obj.magic s_obj in
  GenArg (aat,obj)
*)

(* Not possible like this, must return the wrapped form abstract_argument_type *)
(* let rec genarg_type_of_sexp :                                               *)
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

module SerObj = struct

  type ('raw, 'glb, 'top) obj = ('raw, 'glb, 'top) gen_ser

  let name = "ser_arg"
  let default ga =
    Some {
      raw_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; Atom "raw"; sexp_of_genarg_type ga]));
      glb_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; Atom "glb"; sexp_of_genarg_type ga]));
      top_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; Atom "top"; sexp_of_genarg_type ga]));
    }

end

module SerGen = Register(SerObj)

let register_genser ty obj = SerGen.register0 ty obj

let rec get_gen_ser_ty : type r g t. (r,g,t) Genarg.genarg_type -> (r,g,t) gen_ser =
  fun gt -> match gt with
  | Genarg.ExtraArg _      -> SerGen.obj gt
  | Genarg.ListArg  t      -> gen_ser_list (get_gen_ser_ty t)
  | Genarg.OptArg   t      -> gen_ser_opt  (get_gen_ser_ty t)
  | Genarg.PairArg(t1, t2) -> gen_ser_pair (get_gen_ser_ty t1) (get_gen_ser_ty t2)

let get_gen_ser : type o lvl. (o,lvl) abstract_argument_type -> (o -> t) = fun aty ->
  match aty with
   | Genarg.Rawwit ty -> (get_gen_ser_ty ty).raw_ser
   | Genarg.Glbwit ty -> (get_gen_ser_ty ty).glb_ser
   | Genarg.Topwit ty -> (get_gen_ser_ty ty).top_ser

type 'a generic_argument = 'a Genarg.generic_argument

(* We need to generalize this to use the proper printers for opt *)
let mk_sexparg (lvl, st) so =
  List [Atom "GenArg"; lvl; st; so]

(* XXX: There is still some duplication here in the traversal of g_ty, but
   we can live with that for now.  *)
let sexp_of_genarg_val : type a. a generic_argument -> Sexp.t =
  fun g -> match g with
  | GenArg (g_ty, g_val) ->
    mk_sexparg (sexp_of_abstract_argument_type g_ty) (get_gen_ser g_ty g_val)

let sexp_of_generic_argument : type a. (a -> Sexp.t) -> a Genarg.generic_argument -> Sexp.t =
  fun _level_tag g ->
  sexp_of_genarg_val g

type ('raw, 'glb, 'top) gen_des =
  { raw_des : Sexp.t -> 'raw;
    glb_des : Sexp.t -> 'glb;
    top_des : Sexp.t -> 'top;
  }

let gen_des_list : ('raw, 'glb, 'top) gen_des -> ('raw list, 'glb list, 'top list) gen_des = fun g ->
  let open Sexplib.Conv in
  { raw_des = list_of_sexp g.raw_des;
    glb_des = list_of_sexp g.glb_des;
    top_des = list_of_sexp g.top_des;
  }

let gen_des_opt : ('raw, 'glb, 'top) gen_des -> ('raw option, 'glb option, 'top option) gen_des = fun g ->
  let open Sexplib.Conv in
  { raw_des = option_of_sexp g.raw_des;
    glb_des = option_of_sexp g.glb_des;
    top_des = option_of_sexp g.top_des;
  }

let gen_des_pair : ('raw1, 'glb1, 'top1) gen_des -> ('raw2, 'glb2, 'top2) gen_des ->
  (('raw1 * 'raw2), ('glb1 * 'glb2), ('top1 * 'top2)) gen_des = fun g1 g2 ->
  let open Sexplib.Conv in
  { raw_des = pair_of_sexp g1.raw_des g2.raw_des;
    glb_des = pair_of_sexp g1.glb_des g2.glb_des;
    top_des = pair_of_sexp g1.top_des g2.top_des;
  }

module DesObj = struct

  type ('raw, 'glb, 'top) obj = ('raw, 'glb, 'top) gen_des

  let name = "des_arg"
  let default _ga = None

end

module DesGen = Register(DesObj)

let register_gendes ty obj = DesGen.register0 ty obj

let rec get_gen_des : type r g t. (r,g,t) Genarg.genarg_type -> (r,g,t) gen_des =
  fun gt -> match gt with
  | Genarg.ExtraArg _      -> DesGen.obj gt
  | Genarg.ListArg  t      -> gen_des_list (get_gen_des t)
  | Genarg.OptArg   t      -> gen_des_opt  (get_gen_des t)
  | Genarg.PairArg(t1, t2) -> gen_des_pair (get_gen_des t1) (get_gen_des t2)

let generic_deser : type a. ('b,a) abstract_argument_type -> Sexp.t -> a generic_argument = fun ty s ->
  match ty with
  | Genarg.Rawwit w -> GenArg(ty, (get_gen_des w).raw_des s)
  | Genarg.Glbwit w -> GenArg(ty, (get_gen_des w).glb_des s)
  | Genarg.Topwit w -> GenArg(ty, (get_gen_des w).top_des s)

(* let raw_generic_argument_of_sexp _lvl _sexp : rlevel Genarg.generic_argument =
 *   Obj.magic 0 *)

let generic_argument_of_sexp _lvl sexp : 'a Genarg.generic_argument =
  let _ = generic_deser in
  let _ = argument_type_of_sexp in
  Obj.magic sexp
(*
  (* First step, split the genarg to get the type, level, and content of the genarg *)
  let s_typ, s_obj =
    match sexp with
    | List [Atom "GenArg"; s_typ; s_obj] ->
      s_typ, s_obj
    | _ -> raise (Failure "FIND THE PROPER ERROR")
  in
  (* Deserialize the type *)
  let arg_ty : argument_type = argument_type_of_sexp s_typ in
  (* Now apply the deserializer to the expression *)
  match arg_ty with
   | ArgumentType w -> generic_deser w s_obj
*)

type glob_generic_argument =
  [%import: Genarg.glob_generic_argument]
  [@@deriving sexp]

type raw_generic_argument =
  [%import: Genarg.raw_generic_argument]
  [@@deriving sexp]

type typed_generic_argument =
  [%import: Genarg.typed_generic_argument]
  [@@deriving sexp]

