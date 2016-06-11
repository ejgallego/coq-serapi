.PHONY: clean all toplevel serialize-byte serialize-native

include config.mk

OCB=ocamlbuild
OCB_OPT=-use-ocamlfind -j 4

all: toplevel

serialize-byte:
	OCAMLFIND_IGNORE_DUPS_IN=/home/egallego/.opam/4.03.0/lib/ocaml/compiler-libs/ \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) serialize/sercoq.cma

serialize-native:
	OCAMLFIND_IGNORE_DUPS_IN=/home/egallego/.opam/4.03.0/lib/ocaml/compiler-libs/ \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) serialize/sercoq.cmxa

TARGET=native
toplevel:
	OCAMLFIND_IGNORE_DUPS_IN=/home/egallego/.opam/4.03.0/lib/ocaml/compiler-libs/ \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) sertop/sertop.$(TARGET)

clean:
	$(OCB) $(OCB_OPT) -clean

# Not yet ready ocamlbuild support
all-sub:
	make -C serialize

clean-sub:
	make -C serialize clean
