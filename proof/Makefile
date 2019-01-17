
COQC=coqc
COQPARAMS=-R ~/Repositories/tlc/src TLC

MODULES=Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo Opening.vo \
	FreeVars.vo Environments.vo Subst.vo Wellformedness.vo Weakening.vo \
	Kinding.vo Substitution.vo Subtyping.vo Inversion.vo Coercible.vo \
	Typing.vo Soundness.vo

all: ${MODULES}

%.vo: %.v
	${COQC} ${COQPARAMS} $<

Utilities.vo: Disjoint.vo

Definitions.vo: Cofinite.vo

Opening.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo

FreeVars.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo

Environments.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo

Subst.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo FreeVars.vo Environments.vo

Wellformedness.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo FreeVars.vo Environments.vo Subst.vo

Weakening.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo FreeVars.vo Environments.vo Subst.vo Wellformedness.vo

Substitution.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo FreeVars.vo Environments.vo Subst.vo Wellformedness.vo \
	Weakening.vo

Kinding.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo FreeVars.vo Environments.vo Subst.vo Wellformedness.vo \
	Weakening.vo Substitution.vo

Subtyping.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo FreeVars.vo Environments.vo Subst.vo Wellformedness.vo \
	Weakening.vo Substitution.vo Kinding.vo

Inversion.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo FreeVars.vo Environments.vo Subst.vo Wellformedness.vo \
	Weakening.vo Substitution.vo Kinding.vo Subtyping.vo

Coercible.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo FreeVars.vo Environments.vo Subst.vo Wellformedness.vo \
	Weakening.vo Substitution.vo Kinding.vo Subtyping.vo Inversion.vo

Typing.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo FreeVars.vo Environments.vo Subst.vo Wellformedness.vo \
	Weakening.vo Substitution.vo Kinding.vo Subtyping.vo Inversion.vo \
	Coercible.vo

Soundness.vo: Cofinite.vo Disjoint.vo Utilities.vo Definitions.vo \
	Opening.vo FreeVars.vo Environments.vo Subst.vo Wellformedness.vo \
	Weakening.vo Substitution.vo Kinding.vo Subtyping.vo Inversion.vo \
	Coercible.vo Typing.vo

clean:
	@rm -f *.vo *.glob .*.aux
