open Ppxlib

val python : Deriving.t

module Python_of : sig
  val deriver : Deriving.t
end

module Of_python : sig
  val deriver : Deriving.t
end
