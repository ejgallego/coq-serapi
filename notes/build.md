# Building SerAPI Manually

`sertop` is available for different Coq versions, which each of its
branches targetting the corresponding Coq branch. The current
development branch is `v8.7`, for Coq v8.7. The `v8.8` branch is also
availabe but may not be stable until Coq 8.8 is closer to release.

Basic build instructions are below, the `.travis.yml` files should
contain up-to-date information in any case. We recommend using OPAM to
setup the build environment, however Théo Zimmermann has reported
success in NixOS.

0. The currently supported ocaml version is 4.06.0
   ``$ opam switch 4.06.0 && eval `opam config env` ``. We also assume `COQVER=v8.7`.
1. Install the needed packages:
   `$ opam install ocamlfind ocamlbuild ppx_import ppx_deriving cmdliner core_kernel sexplib ppx_sexp_conv camlp5`.
2. Download and compile coq. We recommend:
   `$ git clone -b ${COQVER} https://github.com/coq/coq.git ~/external/coq-${COQVER} && cd ~/external/coq-${COQVER} && ./configure -local -native-compiler no && make -j $NJOBS`.
3. Type `make SERAPI_COQ_HOME=~/external/coq-${COQVER}` to build `sertop`.

Alternatively, you can build install Coq `>= 8.7.1+1` using OPAM and
build against it using just `make`.

The above instructions assume that you use `~/external/coq-${COQVER}`
directory to place the coq build that SerAPI needs; you can modify
the `SERAPI_COQ_HOME` variable in `Makefile` to make this change
permanent, or override the provided default.

Another alternative is to modify your `findlib.conf` file to add Coq's
path to findlib's search path: for example, edit the file `~/.opam/4.06.0/lib/findlib.conf` and change
`path="/home/egallego/.opam/4.06.0/lib"` by `path="/home/egallego/.opam/4.06.0/lib:/home/egallego/external/coq-v8.7"`.

This is convenient to use `merlin`. If you install Coq globally, these
steps may not be needed, findlib may be able to locate Coq for you;
YMMV.
