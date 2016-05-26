.PHONY: clean all

include config.mk

OCB=ocamlbuild
OCB_OPT=-use-ocamlfind

all:
	OCAMLFIND_IGNORE_DUPS_IN=/home/egallego/.opam/4.03.0+32bit/lib/ocaml/compiler-libs/ \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) serialize/sercoq.cma

clean:
	$(OCB) $(OCB_OPT) -clean

# Not yet ready ocamlbuild support
all-sub:
	make -C serialize

clean-sub:
	make -C serialize clean
