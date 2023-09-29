(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

let check_pending_proofs ~pstate =
  Option.iter (fun _pstate ->
  (* let pfs = Proof_global.get_all_proof_names pstate in *)
  let pfs = [] in
  if not CList.(is_empty pfs) then
    let msg = let open Pp in
      seq [ str "There are pending proofs: "
          ; pfs |> List.rev |> prlist_with_sep pr_comma Names.Id.print; str "."] in
    CErrors.user_err msg
    ) pstate

let save_vo ~doc ?ldir ~pstate ~in_file () =
  let _doc = Stm.join ~doc in
  check_pending_proofs ~pstate;
  let ldir = match ldir with
    | None -> Stm.get_ldir ~doc
    (* EJGA: When in interactive mode, the above won't work due to a
       STM bug, we thus allow SerAPI clients to override it *)
    | Some ldir -> ldir
  in
  let out_vo = Filename.(remove_extension in_file) ^ ".vo" in
  let todo_proofs = Library.ProofsTodoNone in
  let () = Library.save_library_to todo_proofs ~output_native_objects:false ldir out_vo in
  ()
