open Sexplib

module type S = sig

  type t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module type SJ = sig

  include S
  val of_yojson : Yojson.Safe.t -> (t, string) Result.result
  val to_yojson : t -> Yojson.Safe.t
end

module type SJP = sig

  include SJ
  val t_of_python : Py.Object.t -> t
  val python_of_t : t -> Py.Object.t
end

module type S1 = sig

  type 'a t

  val t_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t
  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t

end

module type SJ1 = sig

  include S1

  val of_yojson : (Yojson.Safe.t -> ('a, string) Result.result) -> Yojson.Safe.t -> ('a t, string) Result.result
  val to_yojson : ('a -> Yojson.Safe.t) -> 'a t -> Yojson.Safe.t

end

module type SJP1 = sig

  include SJ1

  val t_of_python : (Py.Object.t -> 'a) -> Py.Object.t -> 'a t
  val python_of_t : ('a -> Py.Object.t) -> 'a t -> Py.Object.t

end
