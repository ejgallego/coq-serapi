(* XXX This will go away soon *)

let coq_init_plugins =
  [ ["syntax"]
  ; ["decl_mode"]
  ; ["cc"]
  ; ["firstorder"]
  ; ["setoid_ring"]
  ; ["extraction"]
  ; ["funind"]
  ; ["quote"]

  ; ["nsatz"]
  ; ["fourier"]
  ; ["omega"]
  ; ["micromega"]
  ; ["romega"]
  ; ["Coq"; "ssrmatching"]
  ]

let coq_init_theories =
  [ ["Init"]
  ; ["Unicode"]
  ; ["Bool"]
  ; ["Logic"]
  ; ["Program"]
  ; ["Classes"]
  ; ["Structures"]
  ; ["Relations"]
  ; ["Setoids"]
  ; ["Arith"]
  ; ["PArith"]
  ; ["NArith"]
  ; ["ZArith"]
  ; ["QArith"]
  ; ["Lists"]
  ; ["Vectors"]
  ; ["Reals"]
  ; ["Sets"]
  ; ["FSets"]
  ; ["MSets"]
  ; ["Sorting"]
  ; ["Wellfounded"]
  ; ["Strings"]

  ; ["Numbers"]
  ; ["Numbers"; "NatInt"]
  ; ["Numbers"; "Natural"; "Abstract"]
  ; ["Numbers"; "Natural"; "Peano"]
  ; ["Numbers"; "Integer"; "Abstract"]
  ]

let coq_prelude_mod path = (Names.(DirPath.make @@ List.rev_map Id.of_string ["Coq";"Init";"Prelude"]),
                            path ^ "/theories/Init/Prelude.vo", Some true)
