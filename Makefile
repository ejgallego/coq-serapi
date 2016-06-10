.PHONY: clean all serialize toplevel

include config.mk

OCB=ocamlbuild
OCB_OPT=-use-ocamlfind

all: serialize toplevel

serialize:
	OCAMLFIND_IGNORE_DUPS_IN=/home/egallego/.opam/4.03.0/lib/ocaml/compiler-libs/ \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) serialize/sercoq.cma

TARGET=byte
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
