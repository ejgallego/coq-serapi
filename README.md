## Serialization for Coq internal structures

This repository contains the beginning of the ppx serialization for
Coq's internal structures.

Most of the code should be eventually incorporated into Coq itself, where only the serialization of the private data structures would be needed.

### Building

OPAM is recommended. You need the following packages:

- ocamlfind
- ppx_import
- sexplib
- ppx_sexp_conv

Edit `config.mk` to point out Coq's location.

### API

For the moment, from/to _sexp_ serialization is provided, the `.mli`
files are self-explanatory.

