.PHONY: clean all serlib sertop sercomp force js-dist js-release build build-install test doc

# Leave empty to use OPAM-installed Coq
SERAPI_COQ_HOME ?=
# SERAPI_COQ_HOME=/home/egallego/external/coq-master/_build/install/default/lib/

ifneq ($SERAPI_COQ_HOME,)
  export OCAMLPATH := $(SERAPI_COQ_HOME):$(OCAMLPATH)
  SP_PKGS=coq-serapi
else
  SP_PKGS=coq-serapi
endif

all: build

GITDEPS=$(ls .git/HEAD .git/index)
sertop/ser_version.ml: $(GITDEPS)
	echo "let ser_git_version = \"$(shell git describe --tags || cat VERSION)\";;" > $@

build:
	dune build --root . --only-packages=$(SP_PKGS) @install

check:
	dune build --root . @check

build-install:
	dune build coq-serapi.install

test:
	dune runtest --root .

doc:
	dune build @doc-private @doc

browser:
	google-chrome _build/default/_doc/_html/index.html

sertop: build
	dune exec -- rlwrap sertop

#####################################################
# Javascript support

#####################################################
# JS

JSDIR=jscoq/coq-libjs
JSFILES=$(addprefix $(JSDIR)/,mutex.js unix.js str.js coq_vm.js)

JSCOQ_DEBUG=no
JSOO_OPTS=
ifeq "${JSCOQ_DEBUG}" "yes"
JSOO_OPTS+= --pretty --noinline --disable shortvar --debug-info
endif

js:
	mkdir -p js

force:

_build/default/sertop/sertop_js.bc: force
	dune build --profile=release sertop/sertop_js.bc

js/sertop_js.js: js _build/default/sertop/sertop_js.bc
	js_of_ocaml --dynlink +nat.js +dynlink.js +toplevel.js $(JSOO_OPTS) $(JSFILES) _build/default/sertop/sertop_js.bc -o js/sertop_js.js

# We cannot use the separate compilation mode due to Coq's VM: libcoqrun.a
js-dune:
	dune build --profile=release sertop/sertop_js.bc.js

js-dist:
	rsync -avp --exclude=.git --delete ~/research/jscoq/coq-pkgs/ js/coq-pkgs

js-release:
	rsync -avp --exclude=*~ --exclude=.git --exclude=README.md --exclude=get-hashes.sh --delete js/ ~/research/jscoq-builds

#####################################################
# Misc

clean:
	rm -f sertop/ser_version.ml
	dune clean

demo-sync:
	rsync -avzp --delete js/ /home/egallego/x80/rhino-hawk/
	cp /home/egallego/x80/rhino-hawk/term.html /home/egallego/x80/rhino-hawk/index.html
