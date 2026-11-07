import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.ManuscriptThresholdTail
import Kr25Ssmxt.Analysis.ManuscriptFixedLevelIntensity
import Kr25Ssmxt.Analysis.ManuscriptPointIntensity

/-! The paper's `δ/(6m)` cutoff tail for every fixed-level component
prefix whose rates satisfy the certified pointwise envelope. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem manuscript_fixed_level_prefix_cutoff_budget
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι))
    (p : ApproxParams) (m count : Nat)
    (hm : 0 < m) (hcount : 0 < count)
    (hcard : Fintype.card ι ≤ count)
    (hsteps : ∀ step ∈ steps,
      step.RateEnvelope 0
        (Real.toNNReal (p.threshold m *
          (1 + p.epsilonPrime) ^ 2 * (1 + p.latticeEta) /
          (2 : Real) ^ (manuscriptDyadicCutoff count - 1)))) :
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : ι → Nat => ∑ i, counts i)).real
          {k : Nat | p.threshold m ≤ (k : Real)} ≤
      p.delta / (6 * m) := by
  let upper := Real.toNNReal (p.threshold m *
    (1 + p.epsilonPrime) ^ 2 * (1 + p.latticeEta) /
    (2 : Real) ^ (manuscriptDyadicCutoff count - 1))
  have hcovered : (fixedLevelCoverage steps ∅).card ≤ count :=
    (Finset.card_le_card (Finset.subset_univ _)).trans
      (by simpa only [Finset.card_univ] using hcard)
  have hfactor : (1 + p.epsilonPrime) ^ 2 *
      (1 + p.latticeEta) ≤ (4 / 3 : Real) := p.upper_intensity_factor
  have hdenom : 0 < (2 : Real) ^ (manuscriptDyadicCutoff count - 1) := by
    positivity
  have hupperNonneg : 0 ≤ p.threshold m *
      (1 + p.epsilonPrime) ^ 2 * (1 + p.latticeEta) /
        (2 : Real) ^ (manuscriptDyadicCutoff count - 1) := by
    have heta : 0 ≤ 1 + p.latticeEta := by
      dsimp [ApproxParams.latticeEta]
      linarith [p.epsilon_pos]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (p.threshold_pos m).le (sq_nonneg _)) heta)
      hdenom.le
  have hupper : (upper : Real) ≤
      (4 / 3) * p.threshold m /
        (2 : Real) ^ (manuscriptDyadicCutoff count - 1) := by
    rw [show (upper : Real) = p.threshold m *
        (1 + p.epsilonPrime) ^ 2 * (1 + p.latticeEta) /
          (2 : Real) ^ (manuscriptDyadicCutoff count - 1) from
      Real.coe_toNNReal _ hupperNonneg]
    have hscale : 0 ≤ p.threshold m /
        (2 : Real) ^ (manuscriptDyadicCutoff count - 1) := by
      exact div_nonneg (p.threshold_pos m).le hdenom.le
    have hmul := mul_le_mul_of_nonneg_right hfactor hscale
    calc
      p.threshold m * (1 + p.epsilonPrime) ^ 2 * (1 + p.latticeEta) /
          (2 : Real) ^ (manuscriptDyadicCutoff count - 1) =
        ((1 + p.epsilonPrime) ^ 2 * (1 + p.latticeEta)) *
          (p.threshold m /
            (2 : Real) ^ (manuscriptDyadicCutoff count - 1)) := by ring
      _ ≤ (4 / 3) *
          (p.threshold m /
            (2 : Real) ^ (manuscriptDyadicCutoff count - 1)) := hmul
      _ = (4 / 3) * p.threshold m /
          (2 : Real) ^ (manuscriptDyadicCutoff count - 1) := by ring
  exact fixedLevelLaw_dyadic_cutoff_budget ι steps count hcount hcovered
    p m hm upper hupper hsteps

end Kr25Ssmxt
