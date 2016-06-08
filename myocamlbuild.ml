open Ocamlbuild_plugin

let coq_location  = "/home/egallego/external/coq-git/"
let opam_location = "/home/egallego/.opam/4.03.0/lib/"

let p s     = coq_location ^ s
let q s lib = coq_location ^ s ^ "/" ^ lib

let () =
  dispatch begin function
    | After_rules ->
      ocaml_lib ~extern:true ~dir:(p "lib")      ~tag_name:"coq_clib"     (q "lib"      "clib");
      ocaml_lib ~extern:true ~dir:(p "lib")      ~tag_name:"coq_lib"      (q "lib"      "lib");

      (* Coq needs this *)
      flag ["link"; "ocaml"; "coq_parsing"; "byte"]   (S [P (opam_location ^ "camlp5/odyl.cma")]);
      flag ["link"; "ocaml"; "coq_parsing"; "byte"]   (S [P (opam_location ^ "camlp5/camlp5.cma")]);

      (* XXX: Native needs dynlink flags *)
      flag ["link"; "ocaml"; "coq_parsing"; "native"] (S [P (opam_location ^ "camlp5/odyl.cmxa")]);
      flag ["link"; "ocaml"; "coq_parsing"; "native"] (S [P (opam_location ^ "camlp5/camlp5.cmxa")]);

      ocaml_lib ~extern:true ~dir:(p "kernel")   ~tag_name:"coq_kernel"   (q "kernel"   "kernel");

      flag ["link"; "ocaml"; "coq_vm"; "byte"]
        (S [A "-I"      ; P (p "kernel/byterun/");
            A "-dllpath"; P (p "kernel/byterun/");
            A "-dllib";   A "-lcoqrun";
            (* A "-cclib";   A "-lcoqrun" *) ]);

      flag ["link"; "ocaml"; "coq_vm"; "native"]
        (S [A "-I"      ; P (p "kernel/byterun/");
            A "-cclib";   A "-lcoqrun"]);

      ocaml_lib ~extern:true ~dir:(p "library")  ~tag_name:"coq_library"  (q "library"   "library");
      ocaml_lib ~extern:true ~dir:(p "intf")     ~tag_name:"coq_intf"     "intf";
      ocaml_lib ~extern:true ~dir:(p "engine")   ~tag_name:"coq_engine"   (q "engine"    "engine");
      ocaml_lib ~extern:true ~dir:(p "pretyping")~tag_name:"coq_pretyping"(q "pretyping" "pretyping");
      ocaml_lib ~extern:true ~dir:(p "interp")   ~tag_name:"coq_interp"   (q "interp"    "interp");

      ocaml_lib ~extern:true ~dir:(p "parsing")  ~tag_name:"coq_parsing"  (q "parsing"   "parsing");
      ocaml_lib ~extern:true ~dir:(p "grammar")  ~tag_name:"coq_grammar"  (q "grammar"   "grammar");
      ocaml_lib ~extern:true ~dir:(p "proofs")   ~tag_name:"coq_proofs"   (q "proofs"    "proofs");
      ocaml_lib ~extern:true ~dir:(p "printing") ~tag_name:"coq_printing" (q "printing"  "printing");
      ocaml_lib ~extern:true ~dir:(p "tactics")  ~tag_name:"coq_tactics"  (q "tactics"   "tactics");
      ocaml_lib ~extern:true ~dir:(p "stm")      ~tag_name:"coq_stm"      (q "stm"       "stm");
      ocaml_lib ~extern:true ~dir:(p "toplevel") ~tag_name:"coq_toplevel" (q "toplevel"  "toplevel");
      ocaml_lib ~extern:true ~dir:(p "parsing")  ~tag_name:"coq_hparsing" (q "parsing"   "highparsing");
      ocaml_lib ~extern:true ~dir:(p "ltac")     ~tag_name:"coq_ltac"     (q "ltac"      "ltac");
    | _ -> ()
  end

module Debug = struct

  let coq_reg tag_name dir libpath =
    Format.printf "registering t: %s, d: %s, lp: %s \n%!" tag_name dir libpath;
    let add_dir x             = S[A"-I"; P dir; x]          in
    let flag_and_dep tags lib = flag tags (add_dir (A lib)) in
    flag_and_dep ["ocaml"; "link"; "byte"]   (libpath^".cma");
    flag_and_dep ["ocaml"; "link"; "native"] (libpath^".cmxa");

end

