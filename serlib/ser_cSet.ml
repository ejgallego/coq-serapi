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

  include CSig.SetS

  include SerType.S with type t := t

end

module Make (M : CSig.SetS) (S : SerType.S with type t := M.elt) = struct

  include M

  let sexp_of_t cst =
    sexp_of_list S.sexp_of_t M.(elements cst)

  let t_of_sexp sexp =
    List.fold_left (fun e s -> M.add s e) M.empty
      (list_of_sexp S.t_of_sexp sexp)

end
