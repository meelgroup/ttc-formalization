import Kr25Ssmxt.Model.Program

/-! # Oracle contracts

The accuracy specifications the analysis proves of TTC's geometric oracles. They are not
part of any public statement, so they live here rather than in `Model/`. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Kr25Ssmxt

/-- Pointwise multiplicative almost-uniformity on one finite lattice set. -/
def AlmostUniformPointwise {n : Nat} (μ : Measure (LatticePoint n))
    (S : Set (LatticePoint n)) (η : Real) : Prop :=
  IsProbabilityMeasure μ ∧ S.Finite ∧ S.Nonempty ∧ μ Sᶜ = 0 ∧
    ∀ x ∈ S, μ.real {x} ∈ Arlib.relErr η (1 / S.ncard)

/-- The required relative-volume guarantee for every call made in this TTC run. -/
def ComputeVolumeContract {n k : Nat} (O : TTCOracles n k)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) : Prop :=
  let D := O.preprocessing.run F hbounded
  ∀ i,
    let law := O.computeVolume (D.component i) p.epsilonPrime
      (p.deltaPrime D.componentCount)
    IsProbabilityMeasure law ∧
      law.real {o | o.1 = false} ≤ p.deltaPrime D.componentCount ∧
      ∀ᵐ o ∂law, o.1 = true →
        (o.2 : Real) ∈ Arlib.relErr p.epsilonPrime
          (volume (D.component i).carrier).toReal

end Kr25Ssmxt
