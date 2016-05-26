.PHONY: clean all

include config.mk

OCB=ocamlbuild
OCB_OPT=-use-ocamlfind

all:
	make -C serialize

clean:
	make -C serialize clean

# Not yet ready ocamlbuild support
ocb:
	OCAMLFIND_IGNORE_DUPS_IN=/home/egallego/.opam/4.03.0+32bit/lib/ocaml/compiler-libs/ \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) serialize/sercoq.cma

ocb-clean:
	$(OCB) $(OCB_OPT) -clean
