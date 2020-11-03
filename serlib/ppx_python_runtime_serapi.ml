include Ppx_python_runtime
(* To remove in newer ppx_python release *)
exception Not_found_s = Base.Not_found_s

let python_of_unit _ = Py.Int.of_int 0
let unit_of_python _ = ()
