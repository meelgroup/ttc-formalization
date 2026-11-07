import Kr25Ssmxt.Model.Prelude

/-! Quantities used inside the proofs of the headline theorems but not in their
statements: the two geometric precision requirements derived from `getprec`,
and the precision scale of the runtime bound before `b` is eliminated. -/

noncomputable section

namespace Kr25Ssmxt

/-- The lattice comparison parameter `η = ε / 8`. -/
def ApproxParams.latticeEta (p : ApproxParams) : Real := p.epsilon / 8

/-- The stronger inball size required by the pointwise lattice sampler. -/
def samplerRadiusRequirement {n : Nat} (P : PolytopeData n) (η : Real) : Real :=
  (512 * n / η) *
    Real.sqrt (Real.log (32 * P.presentation.facetCount / η))

/-- The precision scale `1 + b + log⁺ R_max` of the runtime bound at precision `b`. -/
def TTCRuntime.theorem3PrecisionScale (b : Nat) (outerRadiusMax : Real) : Real :=
  1 + b + max 0 (Real.log outerRadiusMax)

end Kr25Ssmxt
