#!/bin/bash

OCAML_VER=4.04.0

# build 32 bits parts
opam switch $OCAML_VER+32bit
eval `opam config env`

make sertop_js.byte

if [ $? -ne 0 ]; then
   exit $?
fi

# Switch back to 64 bit env?
# opam switch $OCAML_VER
# eval `opam config env`

make js/sertop_js.js

