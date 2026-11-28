/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Model.Theorem

/-! Regression checks for both sealed TTC guarantees at the minimum dimension. -/

namespace ttcTest

open ttc MeasureTheory
open scoped ENNReal

example {k : ℕ} (F : LRAFormula 3 k) (hb : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor 3 k) :
    (SealedRun.estimate F hb p prep).real
      {e | (e : ℝ) ∈ Arlib.relErr p.epsilon (volume (solutionSet F)).toReal} ≥ 1 - p.delta :=
  ttc_theorem1_volume_accuracy (by decide) F hb p prep

example : ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} (F : LRAFormula 3 k)
    (hb : Bornology.IsBounded (solutionSet F)) (p : ApproxParams) (prep : TTCPreprocessor 3 k),
    SealedRun.expectedOperations F hb p prep ≤
      ENNReal.ofReal (C * ttcRuntimeRate (prep.run F hb) p) := by
  obtain ⟨C, hC, h⟩ := ttc_theorem3_expected_runtime
  exact ⟨C, hC, fun F hb p prep => h (by decide) F hb p prep⟩

end ttcTest
