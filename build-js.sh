#!/bin/bash

OCAML_VER=4.02.3

# build 32 bits parts
opam switch $OCAML_VER+32bit
eval `opam config env`

make sertop_js.byte

if [ $? -ne 0 ]; then
   exit $?
fi

# opam switch $OCAML_VER
# eval `opam config env`

make js/sertop_js.js

