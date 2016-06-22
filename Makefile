.PHONY: clean all toplevel serlib sertop

include config.mk

OCB=ocamlbuild
OCB_OPT=-use-ocamlfind -j 4 #-classic-display

all: sertop

TARGET=native

ifeq "${TARGET}" "native"
CMAEXT=cmxa
else
CMAEXT=cma
endif

serlib:
	OCAMLFIND_IGNORE_DUPS_IN=/home/egallego/.opam/4.03.0/lib/ocaml/compiler-libs/ \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) serlib/serlib.$(CMAEXT)

sertop:
	OCAMLFIND_IGNORE_DUPS_IN=/home/egallego/.opam/4.03.0/lib/ocaml/compiler-libs/ \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) sertop/sertop.$(TARGET)

clean:
	$(OCB) $(OCB_OPT) -clean

# Not yet ready ocamlbuild support
all-sub:
	make -C serlib

clean-sub:
	make -C serlib clean
