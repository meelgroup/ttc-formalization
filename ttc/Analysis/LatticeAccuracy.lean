import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.TtcVolumeAccuracyLatticeComparison
import ttc.Analysis.TheoremProof
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The deterministic final step of paper Theorem 1, independent of the
streaming implementation used to estimate the finite lattice count. -/

namespace ttc

open MeasureTheory

theorem lattice_accuracy_from_count
    {n k : Nat} {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (μ : Measure NNReal) [IsProbabilityMeasure μ]
    (hcomparison : (volume D.union).toReal ∈
      Arlib.relErr p.latticeEta
        ((D.latticePoints b).ncard / (10 : Real) ^ (b * n)))
    (hcount : μ.real
      {estimate | (estimate : Real) ∈ Arlib.relErr (p.epsilon / 2)
        ((D.latticePoints b).ncard / (10 : Real) ^ (b * n))} ≥
        1 - p.delta) :
    μ.real {estimate | (estimate : Real) ∈
      Arlib.relErr p.epsilon (volume (solutionSet F)).toReal} ≥
        1 - p.delta := by
  let q : Real := (D.latticePoints b).ncard / (10 : Real) ^ (b * n)
  let V : Real := (volume D.union).toReal
  have hvolumeEq : volume D.union = volume (solutionSet F) :=
    D.volume_eq_solutionSet
  rw [← hvolumeEq]
  change V ∈ Arlib.relErr p.latticeEta q at hcomparison
  change μ.real
      {estimate | (estimate : Real) ∈ Arlib.relErr (p.epsilon / 2) q} ≥
    1 - p.delta at hcount
  apply hcount.trans
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro estimate hestimate
  rw [show p.latticeEta = p.epsilon / 8 by rfl] at hcomparison
  change (1 - p.epsilon / 2) * q ≤ (estimate : Real) ∧
    (estimate : Real) ≤ (1 + p.epsilon / 2) * q at hestimate
  change (1 - p.epsilon) * V ≤ (estimate : Real) ∧
    (estimate : Real) ≤ (1 + p.epsilon) * V
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hone_sub : 0 ≤ 1 - p.epsilon := sub_nonneg.mpr p.epsilon_le_one
  have hone_add : 0 ≤ 1 + p.epsilon := by nlinarith [p.epsilon_pos]
  constructor
  · calc
      (1 - p.epsilon) * V ≤
          (1 - p.epsilon) * ((1 + p.epsilon / 8) * q) :=
        mul_le_mul_of_nonneg_left hcomparison.2 hone_sub
      _ ≤ (1 - p.epsilon / 2) * q := by
        nlinarith [p.epsilon_pos, p.epsilon_le_one]
      _ ≤ (estimate : Real) := hestimate.1
  · calc
      (estimate : Real) ≤ (1 + p.epsilon / 2) * q := hestimate.2
      _ ≤ (1 + p.epsilon) * ((1 - p.epsilon / 8) * q) := by
        nlinarith [p.epsilon_pos, p.epsilon_le_one]
      _ ≤ (1 + p.epsilon) * V :=
        mul_le_mul_of_nonneg_left hcomparison.1 hone_add

end ttc
