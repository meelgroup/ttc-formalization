import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.ThresholdTail
import ttc.Analysis.FixedLevelIntensity
import ttc.Analysis.PointIntensity

/-! The paper's `δ/(6m)` cutoff tail for every fixed-level component
prefix whose rates satisfy the certified pointwise envelope. -/

namespace ttc

open MeasureTheory

theorem fixed_level_prefix_cutoff_budget
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι))
    (p : ApproxParams) (m count : Nat)
    (hm : 0 < m) (hcount : 0 < count)
    (hcard : Fintype.card ι ≤ count)
    (hsteps : ∀ step ∈ steps,
      step.RateEnvelope 0
        (Real.toNNReal (p.Thresh m *
          (1 + p.ε') ^ 2 * (1 + p.latticeEta) /
          (2 : Real) ^ (dyadicCutoff count - 1)))) :
    ((fixedLevelLaw steps
      (Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0))).map
        (fun counts : ι → Nat => ∑ i, counts i)).real
          {k : Nat | p.Thresh m ≤ (k : Real)} ≤
      p.delta / (6 * m) := by
  let upper := Real.toNNReal (p.Thresh m *
    (1 + p.ε') ^ 2 * (1 + p.latticeEta) /
    (2 : Real) ^ (dyadicCutoff count - 1))
  have hcovered : (fixedLevelCoverage steps ∅).card ≤ count :=
    (Finset.card_le_card (Finset.subset_univ _)).trans
      (by simpa only [Finset.card_univ] using hcard)
  have hfactor : (1 + p.ε') ^ 2 *
      (1 + p.latticeEta) ≤ (4 / 3 : Real) := p.upper_intensity_factor
  have hdenom : 0 < (2 : Real) ^ (dyadicCutoff count - 1) := by
    positivity
  have hupperNonneg : 0 ≤ p.Thresh m *
      (1 + p.ε') ^ 2 * (1 + p.latticeEta) /
        (2 : Real) ^ (dyadicCutoff count - 1) := by
    have heta : 0 ≤ 1 + p.latticeEta := by
      dsimp [ApproxParams.latticeEta]
      linarith [p.epsilon_pos]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (p.threshold_pos m).le (sq_nonneg _)) heta)
      hdenom.le
  have hupper : (upper : Real) ≤
      (4 / 3) * p.Thresh m /
        (2 : Real) ^ (dyadicCutoff count - 1) := by
    rw [show (upper : Real) = p.Thresh m *
        (1 + p.ε') ^ 2 * (1 + p.latticeEta) /
          (2 : Real) ^ (dyadicCutoff count - 1) from
      Real.coe_toNNReal _ hupperNonneg]
    have hscale : 0 ≤ p.Thresh m /
        (2 : Real) ^ (dyadicCutoff count - 1) := by
      exact div_nonneg (p.threshold_pos m).le hdenom.le
    have hmul := mul_le_mul_of_nonneg_right hfactor hscale
    calc
      p.Thresh m * (1 + p.ε') ^ 2 * (1 + p.latticeEta) /
          (2 : Real) ^ (dyadicCutoff count - 1) =
        ((1 + p.ε') ^ 2 * (1 + p.latticeEta)) *
          (p.Thresh m /
            (2 : Real) ^ (dyadicCutoff count - 1)) := by ring
      _ ≤ (4 / 3) *
          (p.Thresh m /
            (2 : Real) ^ (dyadicCutoff count - 1)) := hmul
      _ = (4 / 3) * p.Thresh m /
          (2 : Real) ^ (dyadicCutoff count - 1) := by ring
  exact fixedLevelLaw_dyadic_cutoff_budget ι steps count hcount hcovered
    p m hm upper hupper hsteps

end ttc
