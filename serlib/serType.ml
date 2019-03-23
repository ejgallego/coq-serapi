open Sexplib

module type S = sig

  type t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module type S1 = sig

  type 'a t

  val t_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t
  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t

end
