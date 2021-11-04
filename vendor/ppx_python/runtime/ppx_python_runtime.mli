open Pytypes

val python_of_bool : bool -> pyobject
val bool_of_python : pyobject -> bool
val python_of_int : int -> pyobject
val int_of_python : pyobject -> int
val python_of_float : float -> pyobject
val float_of_python : pyobject -> float
val python_of_string : string -> pyobject
val string_of_python : pyobject -> string
val python_of_array : ('a -> pyobject) -> 'a array -> pyobject
val array_of_python : (pyobject -> 'a) -> pyobject -> 'a array
val python_of_list : ('a -> pyobject) -> 'a list -> pyobject
val list_of_python : (pyobject -> 'a) -> pyobject -> 'a list
val python_of_option : ('a -> pyobject) -> 'a option -> pyobject
val option_of_python : (pyobject -> 'a) -> pyobject -> 'a option

module Dict_str_keys : sig
  type t = pyobject

  val create : (string * pyobject) list -> t
  val set : t -> string -> pyobject -> unit
  val find : t -> string -> pyobject
end

exception Not_found_s of Base.Sexp.t
