## Serialization for Coq internal structures and Protocol Playground

This repository contains the beginning of the ppx serialization for Coq's internal structures.

Most of the code should be eventually incorporated into Coq itself, where only the serialization of the private data structures would be needed.

### Building

OPAM and ocamlbuild are required. You need the following packages:

- ocamlfind
- ppx_import
- sexplib
- ppx_sexp_conv

Edit `myocamlbuild.ml` to add the location of Coq and opam sources. Then, make will do the rest.

### API

For the moment, from/to _sexp_ serialization is provided, the `.mli` files are self-explanatory.

### Toplevel

A basic toplevel based in the serializers is in progress.


