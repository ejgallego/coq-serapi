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

# build is required as otherwise the serlib plugins won't be in scope
# for testing; we should really add the package dep to dune test files
test: build
	dune runtest --root .

doc:
	dune build @doc-private @doc

browser:
	google-chrome _build/default/_doc/_html/index.html

sertop: build
	dune exec -- rlwrap sertop

#####################################################
# Misc

clean:
	rm -f sertop/ser_version.ml
	dune clean

demo-sync:
	rsync -avzp --delete js/ /home/egallego/x80/rhino-hawk/
	cp /home/egallego/x80/rhino-hawk/term.html /home/egallego/x80/rhino-hawk/index.html
