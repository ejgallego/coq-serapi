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

  let from_list = List.fold_left (fun e s -> M.add s e) M.empty

  let sexp_of_t cst =
    sexp_of_list S.sexp_of_t M.(elements cst)

  let t_of_sexp sexp =
    from_list (list_of_sexp S.t_of_sexp sexp)

end

module type ExtSJ = sig

  include CSig.SetS

  include SerType.SJ with type t := t

end

module MakeJ (M : CSig.SetS) (S : SerType.SJ with type t := M.elt) = struct

  include Make(M)(S)

  let to_yojson cst =
    `List (List.map S.to_yojson M.(elements cst))

  let of_yojson json =
    let open Ppx_deriving_yojson_runtime in
    let json = Yojson.Safe.Util.to_list json in
    map_bind S.of_yojson [] json >|= from_list

end
