
COQC=coqc
COQPARAMS=-R ~/Repositories/tlc/src TLC

MODULES=Cofinite.vo Definitions.vo Infrastructure.vo Kinding.vo

all: ${MODULES}

%.vo: %.v
	${COQC} ${COQPARAMS} $<

Infrastructure.vo: Definitions.vo
Kinding.vo: Definitions.vo Infrastructure.vo

clean:
	@rm -f *.vo *.glob .*.aux
