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
(* Status: Experimental                                                 *)
(************************************************************************)

module Vmemitcodes = Ser_vmemitcodes

module OP = struct
type t = Vmlibrary.t
let name = "Vmlibrary.t"
end

module B = SerType.Opaque(OP)
type t = B.t
 [@@deriving sexp,yojson,hash,compare]

module OQ = struct
type t = Vmlibrary.index
let name = "Vmlibrary.index"
end

module C = SerType.Opaque(OQ)
type index = C.t
 [@@deriving sexp,yojson,hash,compare]

type indirect_code = index Vmemitcodes.pbody_code [@@deriving sexp,yojson,hash,compare]
