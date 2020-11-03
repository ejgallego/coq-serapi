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

module type ExtS = sig

  include CSig.MapS

  (* module SSet : Ser_cSet.ExtS *)

  include SerType.S1 with type 'a t := 'a t

end

module Make (M : CSig.MapS) (S : SerType.S with type t := M.key)
  : ExtS
    with type key = M.key
     and type 'a t = 'a M.t
     (* and module Set := M.Set *)

module type ExtSJ = sig

  include CSig.MapS

  include SerType.SJ1 with type 'a t := 'a t

end

module MakeJ (M : CSig.MapS) (S : SerType.SJ with type t := M.key)
  : ExtSJ
    with type key = M.key
     and type 'a t = 'a M.t

module type ExtSJP = sig

  include CSig.MapS

  include SerType.SJP1 with type 'a t := 'a t

end

module MakeJP (M : CSig.MapS) (S : SerType.SJP with type t := M.key)
  : ExtSJP
    with type key = M.key
     and type 'a t = 'a M.t
