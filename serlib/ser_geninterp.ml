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

open Sexplib.Conv
open Ppx_python_runtime
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Names      = Ser_names

module Val = struct

  type 'a typ =
    [%import: 'a Geninterp.Val.typ]

  (* let typ_of_sexp _ _ = Serlib_base.opaque_of_sexp "Geninterp.Val.typ" *)
  let sexp_of_typ _ x = Serlib_base.sexp_of_opaque ~typ:"Geninterp.Val.typ" x
  let _python_of_typ _ x = Serlib_base.python_of_opaque ~typ:"Geninterp.Val.typ" x

  type t =
    [%import: Geninterp.Val.t]
    [@@deriving sexp_of]

  let t_of_sexp x = Serlib_base.opaque_of_sexp ~typ:"Geninterp.Val.t" x
  let python_of_t x = Serlib_base.python_of_opaque ~typ:"Geninterp.Val.t" x
  let t_of_python x = Serlib_base.opaque_of_python ~typ:"Geninterp.Val.t" x
  let of_yojson = Serlib_base.opaque_of_yojson ~typ:"Geninterp.Val.t"
  let to_yojson x = Serlib_base.opaque_to_yojson ~typ:"Geninterp.Val.t" x

  let hash = Hashtbl.hash
  let hash_fold_t st d = Ppx_hash_lib.Std.Hash.Builtin.hash_fold_int st (Hashtbl.hash d)
  let compare = Stdlib.compare

end

module TacStore = struct
  type t = Geninterp.TacStore.t
  let t_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Geninterp.TacStore.t"
  let sexp_of_t = Serlib_base.sexp_of_opaque ~typ:"Geninterp.TacStore.t"
  let t_of_python = Serlib_base.opaque_of_python ~typ:"Geninterp.TacStore.t"
  let python_of_t = Serlib_base.python_of_opaque ~typ:"Geninterp.TacStore.t"
  let to_yojson = Serlib_base.opaque_to_yojson ~typ:"Geninterp.TacStore.t"
  let of_yojson = Serlib_base.opaque_of_yojson ~typ:"Geninterp.TacStore.t"
  let _hash = Hashtbl.hash
  let hash_fold_t st d = Ppx_hash_lib.Std.Hash.Builtin.hash_fold_int st (Hashtbl.hash d)
  let compare = Stdlib.compare
end

type interp_sign =
  [%import: Geninterp.interp_sign]
  [@@deriving sexp,yojson,python,hash,compare]
