(* XXX This will go away soon *)

let coq_init_plugins =
  [ ["syntax"]
  ; ["ltac"]
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

  ; ["Numbers"; "Cyclic"; "Abstract"]
  ; ["Numbers"; "Cyclic"; "DoubleCyclic"]
  ; ["Numbers"; "Cyclic"; "Int31"]
  ; ["Numbers"; "Cyclic"; "ZModulo"]

  ; ["Numbers"; "Integer"; "Abstract"]
  ; ["Numbers"; "Integer"; "BigZ"]
  ; ["Numbers"; "Integer"; "Binary"]
  ; ["Numbers"; "Integer"; "NatPairs"]
  ; ["Numbers"; "Integer"; "SpecViaZ"]

  ; ["Numbers"; "NatInt"]

  ; ["Numbers"; "Natural"; "Abstract"]
  ; ["Numbers"; "Natural"; "BigN"]
  ; ["Numbers"; "Natural"; "Binary"]
  ; ["Numbers"; "Natural"; "Peano"]
  ; ["Numbers"; "Natural"; "SpecViaZ"]

  ; ["Numbers"; "Rational"; "BigQ"]
  ; ["Numbers"; "Rational"; "SpecViaQ"]

  ]

let coq_prelude_mod path = (Names.(DirPath.make @@ List.rev_map Id.of_string ["Coq";"Init";"Prelude"]),
                            path ^ "/theories/Init/Prelude.vo", Some true)
