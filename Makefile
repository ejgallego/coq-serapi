.PHONY: clean all

include config.mk

FILES=ser_bigint ser_loc ser_flags ser_goptions ser_names ser_univ	\
      ser_conv_oracle ser_globnames ser_misctypes ser_decl_kinds	\
      ser_genarg ser_evar_kinds ser_tok ser_extend ser_stateid		\
      ser_glob_term ser_libnames ser_constrexpr ser_tacexpr		\
      ser_vernacexpr

# Old-style stuff, needs review
DUM=ser_constr ser_goal

MLI=$(addsuffix .cmi, $(FILES) $(DUM))
OBJS=$(addsuffix .cmo, $(FILES) $(DUM))

all: $(MLI) $(OBJS)

# Include coq files
INCLUDETOP=-I $(COQDIR)/library/   \
           -I $(COQDIR)/stm/       \
           -I $(COQDIR)/lib/       \
           -I $(COQDIR)/parsing/   \
           -I $(COQDIR)/printing/  \
           -I $(COQDIR)/kernel/    \
           -I $(COQDIR)/intf/      \
           -I $(COQDIR)/interp/    \
           -I $(COQDIR)/proofs/    \
           -I $(COQDIR)/toplevel   \
           -I $(COQDIR)/config

CAMLDEBUG=
# CAMLDEBUG=-g
CAMLWARN=-w @a-44-45-4
BYTEFLAGS=-rectypes -safe-string $(CAMLDEBUG) $(CAMLWARN)

SERFLAGS=-package ppx_import,sexplib,ppx_sexp_conv

# Our OCAML rules, we could refine the includes
%.cmi: %.mli
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(SERFLAGS) $<

%.cmo: %.ml
	ocamlfind ocamlc -c $(BYTEFLAGS) $(INCLUDETOP) $(SERFLAGS) $<

########################################################################
# Main coq-serapi files
COQDEPS=$(COQDIR)/lib/clib.cma			\
	$(COQDIR)/lib/lib.cma			\
	$(COQDIR)/kernel/byterun/dllcoqrun.so	\
	$(COQDIR)/kernel/kernel.cma		\
	$(COQDIR)/library/library.cma		\
	$(COQDIR)/pretyping/pretyping.cma	\
	$(COQDIR)/interp/interp.cma		\
	$(COQDIR)/proofs/proofs.cma		\
	$(COQDIR)/parsing/parsing.cma		\
	$(COQDIR)/printing/printing.cma		\
	$(COQDIR)/tactics/tactics.cma		\
	$(COQDIR)/stm/stm.cma			\
	$(COQDIR)/toplevel/toplevel.cma		\
	$(COQDIR)/parsing/highparsing.cma	\
	$(COQDIR)/tactics/hightactics.cma
	# $(COQDIR)/engine/engine.cma		\

clean:
	rm -f *.cmi *.cmo *.ml.d *.mli.d *.cmt *.cmx
