import Kr25Ssmxt.Model.Prelude

/-! Quantities used inside the proofs of the headline theorems but not in their
statements: the two geometric precision requirements derived from `getprec`,
and the precision scale of the runtime bound before `b` is eliminated. -/

noncomputable section

namespace Kr25Ssmxt

/-- The lattice comparison parameter `η = ε / 8`. -/
def ApproxParams.latticeEta (p : ApproxParams) : Real := p.epsilon / 8

/-- The precision scale `1 + b + log⁺ R_max` of the runtime bound at precision `b`. -/
def TTCRuntime.theorem3PrecisionScale (b : Nat) (outerRadiusMax : Real) : Real :=
  1 + b + max 0 (Real.log outerRadiusMax)

/-- The specification of `GetPrecision(F_d, M, η)` (Algorithm `getprec`): at precision `b`
every scaled component has inradius at least `γ = (64 m n / η) √(log (4 r / η))`, with `r`
the total facet count.  TTC uses it at `η = ε / 96`. -/
def PrecisionAdequate {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (b : Nat) (η : Real) : Prop :=
  ∀ i, latticeRadiusRequirement D η ≤ (10 : Real) ^ b * (D.component i).inradius

end Kr25Ssmxt
