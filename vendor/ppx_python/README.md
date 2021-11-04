ppx_python
==========

Generate functions to convert OCaml values to/from Python values.

`ppx_python` is a PPX syntax extension that generates code for
converting OCaml types to and from Python. This uses
the [pyml OCaml bindings for Python](https://github.com/thierry-martinez/pyml/)
to start a Python runtime, create the Python objects or analyze
them.

Usage
-----

Annotate the type with `[@@deriving python]` as in the following example.

```ocaml
let () =
  if not (Pyml.Py.is_initialized ())
  then Pyml.Py.initialize ~version:3 ()
;;

type int_pair = (int * int) [@@deriving python];;
```

This results in two functions being created automatically, `python_of_int_pair` and `int_pair_of_python`
with the following types.

```ocaml
val python_of_int_pair: int_pair -> pyobject
val int_pair_of_python: pyobject -> int_pair
```

If only one direction is needed it is possible to write one of the following.

```ocaml
type int_pair = (int * int) [@@deriving python_of]
type int_pair = (int * int) [@@deriving of_python]
```

Python converters for primitive types such as `int`, `float`, `bool`, or `string` are automatically brought into
scope.

It is also possible to construct converters based on type expressions as in the following example.

```ocaml
let pyobject = [%python_of: (int * string) list] [ 1, "one"; 2, "two" ];;

Stdio.printf "pyobject: %s\n" (Pyml.Py.Object.to_string pyobject);;

let list = [%of_python: (int * string) list] pyobject;;
```

Conversions
-----------

The conversion is straightforward for basic types such as `int`, `float`, `bool`, or `string`.
`unit` is converted to `None`.

OCaml tuples are converted into Python tuples. OCaml lists and arrays are converted in Python lists.

For options, `None` is used on the Python side to represent the `None` case. Otherwise the value is
directly available. Note that this makes ocaml values `Some None` and `None` indistinguishable on the
Python side.

Records are represented using Python dictionaries which keys are strings. The `[@python.default]`
attribute can be used on some of the fields: these fields are then optional on the Python side
and if not present the default value gets used.

```ocaml
type t =
  { foo : int [@python.default 42]
  ; bar : float
  } [@@deriving python]
```

Variants don't have an idiomatic Python representation. They get converted to a pair where the first
element is the constructor as a string and the second element is the content of the variant or `None`
if this variant case does not embed any data.

Below are some more involved usage examples taken from the test suite.

```ocaml
type t =
  { field_a : int
  ; field_b : string
  }
[@@deriving python]

type u =
  { foo : int * int
  ; bar : t
  }
[@@deriving python]

type v =
  | A
  | B of string
  | C of int
  | D of t * string
  | E of
      { x : int
      ; y : string
      }
[@@deriving python]

type 'a w =
  | One of 'a
  | Multi of 'a list
[@@deriving python]

type 'a tree =
  | Leaf of 'a
  | Node of 'a tree * 'a tree
[@@deriving python]
```
