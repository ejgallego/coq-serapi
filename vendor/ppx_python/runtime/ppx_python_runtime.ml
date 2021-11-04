open! Base


let python_of_bool = Py.Bool.of_bool
let bool_of_python = Py.Bool.to_bool
let python_of_int = Py.Int.of_int
let int_of_python = Py.Int.to_int
let python_of_float = Py.Float.of_float
let float_of_python = Py.Float.to_float
let python_of_string = Py.String.of_string
let string_of_python = Py.String.to_string
let python_of_array = Py.List.of_array_map
let array_of_python = Py.List.to_array_map
let python_of_list = Py.List.of_list_map
let list_of_python = Py.List.to_list_map

let python_of_option f = function
  | None -> Py.none
  | Some v -> f v
;;

let option_of_python f pyobject =
  if Caml.( = ) pyobject Py.none then None else Some (f pyobject)
;;

module Dict_str_keys = struct
  type t = Pytypes.pyobject

  let internalized_keys = Hashtbl.create (module String)

  let internalized_key key =
    Hashtbl.findi_or_add internalized_keys key ~default:python_of_string
  ;;

  let set t key value =
    let key = internalized_key key in
    Py.Dict.set_item t key value
  ;;

  let find t key =
    let key = internalized_key key in
    Py.Dict.find t key
  ;;

  let create assoc =
    let t = Py.Dict.create () in
    List.iter assoc ~f:(fun (key, value) -> set t key value);
    t
  ;;
end

exception Not_found_s = Not_found_s
