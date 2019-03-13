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

open Sexplib
open Sexplib.Conv

module type SerType = sig

  type t
  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module type ExtS = sig

  include CSig.MapS

  val t_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t
  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t

end

module Make (M : CSig.MapS) (S : SerType with type t := M.key) = struct

  include M

  let sexp_of_t f cst =
    sexp_of_list (Sexplib.Conv.sexp_of_pair S.sexp_of_t f) M.(bindings cst)

  let t_of_sexp f sexp =
    List.fold_left (fun e (k,s) -> M.add k s e) M.empty
      (list_of_sexp (pair_of_sexp S.t_of_sexp f) sexp)

end
