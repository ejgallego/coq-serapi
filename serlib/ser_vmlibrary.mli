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

type t = Vmlibrary.t
  [@@deriving sexp,yojson,hash,compare]

type index = Vmlibrary.index
  [@@deriving sexp,yojson,hash,compare]

type indirect_code = index Vmemitcodes.pbody_code
  [@@deriving sexp,yojson,hash,compare]
