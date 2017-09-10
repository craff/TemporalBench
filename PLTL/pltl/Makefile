######################################################################
# Makefile (use GNU-Make)
# $* part of the file name that matched the % in the target pattern.
# $@ file name of the target of the rule
# $^ names of the prerequisites
# $< name of the first prerequisite
# $? names of all the prerequisites that are newer than the target
######################################################################


.DEFAULT:
	@echo "This target needs remaking: default = [$<]"
	@echo "No rule provided"


OCAMLC := ocamlc.opt

OCAMLOPT := ocamlopt.opt

OCAMLDEP := ocamldep

OCAMLFLAGS := -g

OCAMLLIBS := unix.cma str.cma

OCAMLOPTFLAGS := $(INCLUDES) -unsafe -inline 100

OCAMLOPTLIBS := unix.cmxa str.cmxa

LIBSMLI := $(patsubst %.mli,%.cmi,$(wildcard *.mli))

LIBSML := $(patsubst %.ml,%.cmo,$(wildcard *.ml))


.PHONY: all libs
all: pltl

libs: $(LIBSMLI) $(LIBSML)

PLTL_OBJS := genAndComp.cmx miscSolver.cmx altGenlex.cmx hashConsing.cmx \
            PLTLFormula.cmx \
            PLTLMisc.cmx PLTLGraph.cmx

PLTLDEBUG_OBJS := genAndComp.cmo miscSolver.cmo altGenlex.cmo hashConsing.cmo \
            PLTLFormula.cmo  \
            PLTLMisc.cmo PLTLGraph.cmo


pltl: $(PLTL_OBJS) pltl.cmx
	$(OCAMLOPT) -o pltl $(OCAMLOPTFLAGS) $(OCAMLOPTLIBS) $^

pltldebug: $(PLTLDEBUG_OBJS) pltl.cmo
	$(OCAMLC) -o pltldebug $(OCAMLFLAGS) $(OCAMLLIBS) $^


%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) $<

%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<


.PHONY: clean
clean:
	find -regextype posix-egrep -regex ".*((\.(cmi|cmo|cma|cmx|o|cmxa))|~)$$" -delete

.PHONY: distclean
distclean: clean
	- rm pltl pltldebug

.PHONY: depend
depend:
	$(OCAMLDEP) *.mli *.ml > .depend

.depend:
	$(OCAMLDEP) *.mli *.ml > .depend

include .depend
