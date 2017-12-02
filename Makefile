
COQC=coqc
COQPARAMS=-R ~/Repositories/tlc/src TLC

MODULES=Cofinite.vo Definitions.vo Substitutions.vo Wellformedness.vo Kinding.vo

all: ${MODULES}

%.vo: %.v
	${COQC} ${COQPARAMS} $<

Substitutions.vo: Definitions.vo
Wellformedness.vo: Definitions.vo Substitutions.vo
Kinding.vo: Definitions.vo Substitutions.vo Wellformedness.vo

clean:
	@rm -f *.vo *.glob .*.aux
