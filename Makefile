TIMEOUT=30
MAXMEM=1000000

depends:
	find . -name \*.pltl -exec echo all: {}.solver {}.bdd {}.tree {}.graph {}.multi > depends \;
	find . -name \*.ctl -exec echo all: {}.solver >> depends \;

include depends

%.pltl.solver: %.pltl
	./run.sh $< "../ModalScp/solver.native" solver ${TIMEOUT} ${MAXMEM}

%.ctl.solver: %.ctl
	./run.sh $< "../ModalScp/solver.native" solver ${TIMEOUT} ${MAXMEM}

%.pltl.bdd: %.pltl
	./run.sh $< "../LTL/bddpltl/bddpltl -sat -silent" bdd ${TIMEOUT} ${MAXMEM}

%.pltl.tree: %.pltl
	./run.sh $< "../LTL/pltlProver/pltl tree" tree ${TIMEOUT} ${MAXMEM}

%.pltl.graph: %.pltl
	./run.sh $< "../LTL/pltlProver/pltl graph" graph ${TIMEOUT} ${MAXMEM}

%.pltl.multi: %.pltl
	./run.sh $< "../LTL/pltl/pltl" multi ${TIMEOUT} ${MAXMEM}

clean:
	find . -name *~ -exec rm {} \;
	find . -name .\#* -exec rm {} \;
	find . -name \#*\# -exec rm {} \;
	- rm ctl/pattern/pattern.cm* ctl/pattern/pattern

veryclean: distclean
	find . -name \*.pltl.\* -exec rm {} \;

distclean: clean
	rm depends
