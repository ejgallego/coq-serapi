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
open Sexplib.Conv

module Names = Ser_names

module RawLevel = struct

  module UGlobal = struct
    type t = Names.DirPath.t * int
    [@@deriving sexp]
  end

  type t =
  | SProp
  | Prop
  | Set
  | Level of UGlobal.t
  | Var of int
  [@@deriving sexp]

end

module Level = struct

  type _t =
    { hash : int
    ; data : RawLevel.t
    }
  [@@deriving sexp]

  type t = Univ.Level.t

  let t_of_sexp sexp  = Obj.magic (_t_of_sexp sexp)
  let sexp_of_t level = sexp_of__t (Obj.magic level)

end

module LSet = Ser_cSet.Make(Univ.LSet)(Level)

type universe_level = Level.t
  [@@deriving sexp]

(* XXX: Think what to do with this  *)
module Universe = struct
  type t = [%import: Univ.Universe.t]

  type _t = (Level.t * int) list
  [@@deriving sexp]

  let t_of_sexp sexp     = Obj.magic (_t_of_sexp sexp)
  let sexp_of_t universe = sexp_of__t (Obj.magic universe)

end

type universe = Universe.t
  [@@deriving sexp]

(*************************************************************************)

module Variance = struct

  type t =
    [%import: Univ.Variance.t]
  [@@deriving sexp]

end

module Instance = struct

type t =
  [%import: Univ.Instance.t]

type _t = Instance of Level.t array
  [@@deriving sexp]

let _instance_put instance            = Instance (Univ.Instance.to_array instance)
let _instance_get (Instance instance) = Univ.Instance.of_array instance

let t_of_sexp sexp     = _instance_get (_t_of_sexp sexp)
let sexp_of_t instance = sexp_of__t (_instance_put instance)

end

type constraint_type =
  [%import: Univ.constraint_type]
  [@@deriving sexp]

type univ_constraint =
  [%import: Univ.univ_constraint]
  [@@deriving sexp]

module Constraint = Ser_cSet.Make(Univ.Constraint)(struct
    let t_of_sexp = univ_constraint_of_sexp
    let sexp_of_t = sexp_of_univ_constraint
  end)

type 'a constrained =
  [%import: 'a Univ.constrained]
  [@@deriving sexp]

module UContext = struct

  type t = Univ.UContext.t

  let t_of_sexp s = Univ.UContext.make (Conv.pair_of_sexp Instance.t_of_sexp Constraint.t_of_sexp s)
  let sexp_of_t t = Conv.sexp_of_pair Instance.sexp_of_t Constraint.sexp_of_t (Univ.UContext.dest t)

end

type universe_context = UContext.t
  [@@deriving sexp]

module AUContext = struct

  type t = Univ.AUContext.t

  (* XXX: Opaque, so check they are the same *)
  let t_of_sexp x = Obj.magic (UContext.t_of_sexp x)
  let sexp_of_t c = UContext.sexp_of_t (Obj.magic c)

end

type abstract_universe_context = AUContext.t
  [@@deriving sexp]

(*
module CumulativityInfo = struct

  type t = Univ.CumulativityInfo.t

  let t_of_sexp s = Univ.CumulativityInfo.make (Conv.pair_of_sexp universe_context_of_sexp (array_of_sexp Variance.t_of_sexp) s)
  let sexp_of_t t =
    Conv.sexp_of_pair sexp_of_universe_context
      (sexp_of_array Variance.sexp_of_t) Univ.CumulativityInfo.(univ_context t, variance t)

end
*)

(* type cumulativity_info = CumulativityInfo.t
 *   [@@deriving sexp] *)

(*
module ACumulativityInfo = struct

  type t = Univ.ACumulativityInfo.t

  let t_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Univ.ACumulativityInfo.t"
  let sexp_of_t = Serlib_base.sexp_of_opaque ~typ:"Univ.ACumulativityInfo.t"

end

*)

module ContextSet = struct
  type t =
    [%import: Univ.ContextSet.t]
    [@@deriving sexp]
end

(* type universe_context_set =
 *   [%import: Univ.universe_context_set] [@warning "-3"]
 *   [@@deriving sexp] *)

type 'a in_universe_context =
  [%import: 'a Univ.in_universe_context]
  [@@deriving sexp]

type 'a in_universe_context_set =
  [%import: 'a Univ.in_universe_context_set]
  [@@deriving sexp]

(* type abstract_cumulativity_info = ACumulativityInfo.t
 *   [@@deriving sexp] *)

type 'a puniverses =
  [%import: 'a Univ.puniverses]
  [@@deriving sexp]

type explanation =
  [%import: Univ.explanation]
  [@@deriving sexp]

(* This problem seems due to packing in OCaml 4.07.0 *)
module Stdlib = struct
module Lazy = struct

  type 'a t = 'a Lazy.t
  let t_of_sexp = lazy_t_of_sexp
  let sexp_of_t = sexp_of_lazy_t

end
end

(* For 4.06.0 *)
module Lazy = Stdlib.Lazy

type univ_inconsistency =
  [%import: Univ.univ_inconsistency]
  [@@deriving sexp]

