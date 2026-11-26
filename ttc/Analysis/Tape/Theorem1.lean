/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Final
import ttc.Model.Theorem

/-!
# Theorem 1 for the sealed program

The sealed program's output law is the old model's (`estimate_eq_ttc`), so Theorem 1 carries
over.
-/

namespace ttc.Tape

/-- **Theorem 1 for the sealed program**: its output is within relative error `ε` of the
volume of the projected solution set with probability at least `1 - δ`. -/
theorem sealed_theorem1_volume_accuracy {n k : Nat} (hn : 21 ≤ n) (F : ttc.LRAFormula n k)
    (hbounded : Bornology.IsBounded (ttc.solutionSet F)) (params : ttc.ApproxParams)
    (prep : ttc.TTCPreprocessor n k) :
    Pr[estimate ← ttc.SealedRun.estimate F hbounded params prep;
      (estimate : Real) ∈
        Arlib.relErr params.epsilon (MeasureTheory.volume (ttc.solutionSet F)).toReal] ≥
      1 - params.delta := by
  rw [estimate_eq_ttc hn]
  exact ttc.ttc_theorem1_volume_accuracy hn F hbounded params prep

end ttc.Tape
