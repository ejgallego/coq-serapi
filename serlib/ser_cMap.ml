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
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv

module type ExtS = sig

  include CSig.MapS

  (* module SSet : Ser_cSet.ExtS *)

  include SerType.S1 with type 'a t := 'a t

end

module Make (M : CSig.MapS) (S : SerType.S with type t := M.key) = struct

  include M

  (* module SSet = Ser_cSet.Make(M.Set)(S) *)

  let sexp_of_t f cst =
    sexp_of_list (Sexplib.Conv.sexp_of_pair S.sexp_of_t f) M.(bindings cst)

  let t_of_sexp f sexp =
    List.fold_left (fun e (k,s) -> M.add k s e) M.empty
      (list_of_sexp (pair_of_sexp S.t_of_sexp f) sexp)

end

module type ExtSJ = sig

  include CSig.MapS

  include SerType.SJ1 with type 'a t := 'a t

end

module MakeJ (M : CSig.MapS) (S : SerType.SJ with type t := M.key) = struct

  include Make(M)(S)

  let tuple_to_yojson f1 f2 (e1, e2) =
    `List [f1 e1; f2 e2]

  let tuple_of_yojson f1 f2 json =
    let tlist = Yojson.Safe.Util.to_list json in
    match tlist with
    | [e1; e2] ->
      let open Ppx_deriving_yojson_runtime in
      f1 e1 >>= (fun r1 ->
      f2 e2 >>= (fun r2 ->
      Ok (r1, r2)))
    | _ ->
      Error "tuple_of_yojson: incorrect number of tuple elements"

  let to_yojson f cst : Yojson.Safe.t =
    `List (List.map (tuple_to_yojson S.to_yojson f) (M.bindings cst))

  let of_yojson f json =
    let open Ppx_deriving_yojson_runtime in
    Yojson.Safe.Util.to_list json |>
    List.fold_left
      (fun e p ->
         e                               >>= (fun e ->
         tuple_of_yojson S.of_yojson f p >|= (fun (k,s) ->
         M.add k s e))) (Ok M.empty)

end

module type ExtSJP = sig

  include CSig.MapS

  include SerType.SJP1 with type 'a t := 'a t

end

module MakeJP (M : CSig.MapS) (S : SerType.SJP with type t := M.key) = struct

  include MakeJ(M)(S)

  let python_of_t f cst =
    Py.List.of_list_map
      (fun (key, binding) ->
         Py.Tuple.of_pair (S.python_of_t key, f binding))
      (M.bindings cst)

  let t_of_python f py =
    List.fold_left (fun e (k,s) -> M.add k s e) M.empty
      (Py.List.to_list_map (fun p ->
           let key, binding = Py.Tuple.to_pair p in
           S.t_of_python key, f binding) py)

end
