
COQC=coqc
COQPARAMS=-R ~/Repositories/tlc/src TLC

MODULES=Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo Substitution.vo \
	Wellformedness.vo Kinding.vo Subtyping.vo Environments.vo \
	Typing.vo Soundness.vo

all: ${MODULES}

%.vo: %.v
	${COQC} ${COQPARAMS} $<

Utilities.vo: Disjoint.vo

Definitions.vo: Cofinite.vo

Substitution.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo

Wellformedness.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Substitution.vo

Kinding.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Substitution.vo Wellformedness.vo

Subtyping.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Substitution.vo Wellformedness.vo Kinding.vo

Ranging.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Substitution.vo Wellformedness.vo Kinding.vo Subtyping.vo

Typing.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Substitution.vo Wellformedness.vo Kinding.vo Subtyping.vo \
	Ranging.vo

Soundness.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Substitution.vo Wellformedness.vo Kinding.vo Subtyping.vo \
	Ranging.vo Typing.vo

clean:
	@rm -f *.vo *.glob .*.aux
