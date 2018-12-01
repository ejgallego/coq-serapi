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
(* Copyright 2016-2018 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let parse_document ~mode ~pp ~doc sid in_pa =

  let stt = ref (doc, sid) in
  try while true do
      let east = Stm.parse_sentence ~doc:(fst !stt) (snd !stt) in_pa in
      stt := Sercomp_lib.process_vernac ~mode ~pp ~doc:(fst !stt) ~st:(snd !stt) east
    done;
    fst !stt
  with Stm.End_of_input -> fst !stt

let sercomp ~mode ~pp ~in_file ~doc ~sid =

  let in_chan = open_in in_file in
  let in_strm = Stream.of_channel in_chan in
  let in_pa   = Pcoq.Parsable.make ~file:(Loc.InFile in_file) in_strm in
  let doc     = parse_document ~mode ~pp ~doc sid in_pa in
  close_in in_chan;
  doc

let _ =
  Sercomp_lib.maincomp ~ext:".v" ~name:"sercomp"
    ~desc:"Experimental Coq Compiler with serialization support."
    ~compfun:sercomp
