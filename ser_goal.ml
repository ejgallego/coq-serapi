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

open Ser_constr

let the_proof () : Term.constr option =
  let open Proof_global in
  try
    let pf = give_me_the_proof ()                                 in
    let (goals, _stack , _shelf, _given_up, sigma ) = Proof.proof pf in
    match goals with
    | []     -> None
    | g :: _ ->
      let g_type = Goal.V82.concl sigma g                   in
      Some g_type
  with NoCurrentProof -> None
      (* let env    = Goal.V82.env   sigma g                           in *)
      (* let _term  = Constrextern.extern_constr true env sigma g_type in *)
      (* let _k     = Term.kind_of_term g_type                         in *)

let sexp_of_proof () =
  Option.cata (fun p -> p |> constr_reify |> sexp_of_coq_constr |> Sexplib.Sexp.to_string)
    "" (the_proof ())

(* let yojson_of_proof () = *)
(*   Option.cata (fun p -> p |> constr_reify |> coq_constr_to_yojson) *)
(*       (`Assoc []) (the_proof ()) *)

(* let json_of_proof () = *)
(*   Option.cata (fun p -> p |> constr_reify |> coq_constr_to_yojson) *)
(*       (`Assoc []) (the_proof ()) *)

(* let string_of_proof () : string = *)
(*   Option.cata Sexplib.Sexp.to_string "" (sexp_of_proof ()) *)

(* let json_of_proof () : json = *)
(*   json_of_proof () *)
