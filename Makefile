TIMEOUT=30
MAXMEM=1000000

all: ./PLTL/bddpltl/bddpltl ./PLTL/pltlProver/pltl ./PLTL/pltl/pltl depends

depends:
	find . -name \*.pltl -exec echo all: {}.solver {}.bdd {}.tree {}.graph {}.multi > depends \;
	find . -name \*.ctl -exec echo all: {}.solver >> depends \;

include depends

%.pltl.solver: %.pltl
	./run.sh $< "../ModalScp/solver.native" solver ${TIMEOUT} ${MAXMEM}

%.ctl.solver: %.ctl
	./run.sh $< "../ModalScp/solver.native" solver ${TIMEOUT} ${MAXMEM}

%.pltl.bdd: %.pltl
	./run.sh $< "./PLTL/bddpltl/bddpltl -sat -silent" bdd ${TIMEOUT} ${MAXMEM}

%.pltl.tree: %.pltl
	./run.sh $< "./PLTL/pltlProver/pltl tree" tree ${TIMEOUT} ${MAXMEM}

%.pltl.graph: %.pltl
	./run.sh $< "./PLTL/pltlProver/pltl graph" graph ${TIMEOUT} ${MAXMEM}

%.pltl.multi: %.pltl
	./run.sh $< "./PLTL/pltl/pltl" multi ${TIMEOUT} ${MAXMEM}

./PLTL/bddpltl/bddpltl:
	cd ./PLTL/bddpltl; make

./PLTL/pltl/pltl:
	cd ./PLTL/pltl; make

./PLTL/pltlProver/pltl:
	cd ./PLTL/pltlProver; make

clean:
	find . -name *~ -exec rm {} \;
	find . -name .\#* -exec rm {} \;
	find . -name \#*\# -exec rm {} \;
	cd ./PLTL/bddpltl; make clean
	cd ./PLTL/pltl; make clean
	cd ./PLTL/pltlProver; make clean
	- rm ctl/pattern/pattern.cm* ctl/pattern/pattern

distclean: clean
	rm depends
	cd ./PLTL/bddpltl; make distclean
	cd ./PLTL/pltl; make distclean
	cd ./PLTL/pltlProver; make distclean

veryveryclean: distclean
	find . -name \*.pltl.\* -exec rm {} \;
