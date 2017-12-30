
COQC=coqc
COQPARAMS=-R ~/Repositories/tlc/src TLC

MODULES=Cofinite.vo Definitions.vo Substitution.vo Wellformedness.vo Kinding.vo

all: ${MODULES}

%.vo: %.v
	${COQC} ${COQPARAMS} $<

Definitions.vo: Cofinite.vo
Substitution.vo: Cofinite.vo Definitions.vo
Wellformedness.vo: Cofinite.vo Definitions.vo Substitution.vo
Kinding.vo: Cofinite.vo Definitions.vo Substitution.vo Wellformedness.vo

clean:
	@rm -f *.vo *.glob .*.aux
