type 'a computation = 'a Future.computation

let computation_of_sexp f x = Future.from_val (f x)
let sexp_of_computation f x = f Future.(force x)
let computation_of_python f x = Future.from_val (f x)
let python_of_computation f x = f Future.(force x)

