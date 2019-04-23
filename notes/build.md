# Building SerAPI Manually

SerAPI is available for different Coq versions, which each of its
branches targetting the corresponding Coq branch. The current
development branch is `v8.9` for Coq v8.9.

Basic build instructions are below, the `.travis.yml` files should
contain up-to-date information in any case. We recommend using OPAM to
setup the build environment, however Théo Zimmermann has reported
success in NixOS.

0. The currently supported ocaml version is 4.06.1 and 4.07.1
   ``$ opam switch 4.07.1 && eval `opam config env` ``. We also assume `COQVER=v8.9`.
1. Install the needed packages:
   `$ opam install dune ppx_import ppx_deriving cmdliner sexplib ppx_sexp_conv camlp5`.
2. Download and compile coq. We recommend:
   `$ git clone -b ${COQVER} https://github.com/coq/coq.git ~/external/coq-${COQVER} && cd ~/external/coq-${COQVER} && ./configure -local -native-compiler no && make -j $NJOBS`.
3. Type `make SERAPI_COQ_HOME=~/external/coq-${COQVER}` to build `sertop`.

Alternatively, you can install Coq `>= 8.9` using OPAM and build against it using just `make`.

The above instructions assume that you use `~/external/coq-${COQVER}`
directory to place the coq build that SerAPI needs; you can modify
the `SERAPI_COQ_HOME` variable in `Makefile` to make this change
permanent, or override the provided default.

SerAPI does use the [Dune](https://github.com/ocaml/dune) build
system, thus standard Dune considerations do apply.

## Executing built binaries

A special consideration is that SerAPI does provide serialization
plugins that are loaded when Coq plugins are. In particular, SerAPI
does use `findlib` to manage plugins' dependencies, so you must
execute `sertop` and `sercomp` using `dune exec` or with the proper
`OCAMLPATH` pointing out to the right install location of Coq.

If that is not properly done, the usual symptom is the error message:
```
(CoqExn "Cannot link ml-object ground_plugin.cmxs to Coq code (Fl_package_base.No_such_package(\"coq-serapi.serlib.ground_plugin\", \"\"))."))
```
When executing binaries via `dune exec`, be sure to pass any arguments after `--`, e.g., `dune exec sercomp -- --help`.
## Advanced Developer Setup

SerAPI builds using Dune which supports modular builds. Starting with
Coq 8.10 you can indeed compose the build of Coq and SerAPI.

This is still experimental; we will provide more details soon.

