.PHONY: clean all serlib sertop sercomp force js-dist js-release

include config.mk

OCB=ocamlbuild
OCB_OPT=-use-ocamlfind -j 4 #-classic-display
OPAMPATH=$(shell opam config var lib)

# Leave empty to use OPAM-installed Coq
SERAPI_COQ_HOME ?=
# SERAPI_COQ_HOME=/home/egallego/external/coq-v8.8/
# SERAPI_COQ_HOME=/home/egallego/research/jscoq/coq-external/coq-v8.7+32bit/

all: sertop sercomp

TARGET=native

ifeq "${TARGET}" "native"
CMAEXT=cmxa
else
CMAEXT=cma
endif

GITDEPS=$(ls .git/HEAD .git/index)
sertop/ser_version.ml: $(GITDEPS)
	echo "let ser_git_version = \"$(shell git describe --tags || cat VERSION)\";;" > $@

serlib:
	OCAMLFIND_IGNORE_DUPS_IN=$(OPAMPATH)/ocaml/compiler-libs/ \
	OCAMLPATH=$(SERAPI_COQ_HOME):$(OCAMLPATH)                 \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) serlib/serlib.$(CMAEXT)

sertop: sertop/ser_version.ml
	OCAMLFIND_IGNORE_DUPS_IN=$(OPAMPATH)/ocaml/compiler-libs/ \
	OCAMLPATH=$(SERAPI_COQ_HOME):$(OCAMLPATH)                 \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) sertop/sertop.$(TARGET)

sercomp: sertop
	OCAMLFIND_IGNORE_DUPS_IN=$(OPAMPATH)/ocaml/compiler-libs/ \
	OCAMLPATH=$(SERAPI_COQ_HOME)                              \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) sertop/sercomp.$(TARGET)


#####################################################
# Javascript support
force:

sertop_js.byte: force
	OCAMLFIND_IGNORE_DUPS_IN=$(OPAMPATH)/ocaml/compiler-libs/ \
	OCAMLPATH=$(SERAPI_COQ_HOME)                              \
	$(OCB) $(OCB_OPT) $(INCLUDETOP) sertop/sertop_js.byte

JSDIR=jscoq/coq-libjs
JSFILES=$(addprefix $(JSDIR)/,mutex.js unix.js str.js coq_vm.js)

js:
	mkdir -p js

js/sertop_js.js: js sertop_js.byte
	js_of_ocaml --dynlink +nat.js +weak.js +dynlink.js +toplevel.js $(JSFILES) sertop_js.byte -o js/sertop_js.js

js-dist:
	rsync -avp --exclude=.git --delete ~/research/jscoq/coq-pkgs/ js/coq-pkgs

js-release:
	rsync -avp --exclude=*~ --exclude=.git --exclude=README.md --exclude=get-hashes.sh --delete js/ ~/research/jscoq-builds

#####################################################
# Misc

clean:
	rm -f sertop/ser_version.ml
	$(OCB) $(OCB_OPT) -clean

# Not yet ready ocamlbuild support
all-sub:
	make -C serlib

clean-sub:
	make -C serlib clean

demo-sync:
	rsync -avzp --delete js/ /home/egallego/x80/rhino-hawk/
	cp /home/egallego/x80/rhino-hawk/term.html /home/egallego/x80/rhino-hawk/index.html
