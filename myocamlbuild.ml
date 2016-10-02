open Ocamlbuild_plugin

let coq_location =
  try
    getenv "SERAPI_COQ_HOME"
  with
    _ -> "/home/egallego/external/coq-master/"

let p s     = coq_location ^ s
let q s lib = coq_location ^ s ^ "/" ^ lib

let () =
  dispatch begin function
    | After_rules ->

      flag ["link"; "ocaml"; "coq_vm"; "byte"]
        (S [A "-I"      ; P (p "kernel/byterun/");
            A "-dllpath"; P (p "kernel/byterun/");
            A "-dllib";   A "-lcoqrun"; ]);

      flag ["link"; "ocaml"; "coq_vm"; "native"]
        (S [A "-I"      ; P (p "kernel/byterun/");
            A "-cclib";   A "-lcoqrun"]);

      flag ["ocaml"; "compile"; "coq_config"] (S [A "-I"; P (p "config")]);

      ocaml_lib ~extern:true ~dir:(p "lib")      ~tag_name:"coq_clib"     (q "lib"      "clib");
      ocaml_lib ~extern:true ~dir:(p "lib")      ~tag_name:"coq_lib"      (q "lib"      "lib");
      ocaml_lib ~extern:true ~dir:(p "kernel")   ~tag_name:"coq_kernel"   (q "kernel"   "kernel");
      ocaml_lib ~extern:true ~dir:(p "library")  ~tag_name:"coq_library"  (q "library"   "library");

      flag ["ocaml"; "compile"; "coq_intf"] (S [A "-I"; P (p "intf")]);

      ocaml_lib ~extern:true ~dir:(p "engine")   ~tag_name:"coq_engine"   (q "engine"    "engine");
      ocaml_lib ~extern:true ~dir:(p "pretyping")~tag_name:"coq_pretyping"(q "pretyping" "pretyping");
      ocaml_lib ~extern:true ~dir:(p "interp")   ~tag_name:"coq_interp"   (q "interp"    "interp");
      ocaml_lib ~extern:true ~dir:(p "grammar")  ~tag_name:"coq_grammar"  (q "grammar"   "grammar");
      ocaml_lib ~extern:true ~dir:(p "proofs")   ~tag_name:"coq_proofs"   (q "proofs"    "proofs");
      ocaml_lib ~extern:true ~dir:(p "parsing")  ~tag_name:"coq_parsing"  (q "parsing"   "parsing");
      ocaml_lib ~extern:true ~dir:(p "printing") ~tag_name:"coq_printing" (q "printing"  "printing");
      ocaml_lib ~extern:true ~dir:(p "tactics")  ~tag_name:"coq_tactics"  (q "tactics"   "tactics");
      ocaml_lib ~extern:true ~dir:(p "vernac")   ~tag_name:"coq_vernac"   (q "vernac"    "vernac");
      ocaml_lib ~extern:true ~dir:(p "stm")      ~tag_name:"coq_stm"      (q "stm"       "stm");
      ocaml_lib ~extern:true ~dir:(p "toplevel") ~tag_name:"coq_toplevel" (q "toplevel"  "toplevel");
      ocaml_lib ~extern:true ~dir:(p "parsing")  ~tag_name:"coq_hparsing" (q "parsing"   "highparsing");
      ocaml_lib ~extern:true ~dir:(p "plugins/ltac") ~tag_name:"coq_ltac" (q "plugins/ltac" "ltac_plugin");
    | _ -> ()
  end
