import ttc.Model.Run
import ttc.Meta.ModelClosure
import ttc.Analysis.Tape.Theorem1
import ttc.Analysis.Tape.AsymptoticRuntime

/-! # Accuracy and arithmetic cost of the sealed TTC run

Both statements are about the same tape execution. Accuracy reads its
estimate and the runtime statement reads its operation tally. Preprocessing
provides the decomposition and LP results. The runtime counts all operations
of the real-RAM model from those inputs, including the draws at their stated
primitive prices.
-/

namespace ttc

open MeasureTheory
open scoped ENNReal

/-- Theorem 1. The sealed estimator achieves relative error `ε` with
probability at least `1 - δ`. -/
theorem ttc_theorem1_volume_accuracy {n k : ℕ} (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams)
    (prep : TTCPreprocessor n k) :
    (SealedRun.estimate F hbounded p prep).real
      {e | (e : ℝ) ∈ Arlib.relErr p.epsilon (volume (solutionSet F)).toReal}
      ≥ 1 - p.delta :=
  Tape.sealed_theorem1_volume_accuracy hn F hbounded p prep

/-- Theorem 3 for the sealed program. For a nonempty decomposition its expected
arithmetic tally is at most `C · m n⁵ ρ² r_max · Λ¹⁰ / ε²`, where `C` is an
absolute constant and `Λ` is the input logarithm in `ttcRuntimeLog`.
The empty decomposition is covered by the same constant. -/
theorem ttc_theorem3_expected_runtime :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n k : ℕ}, 21 ≤ n → ∀ (F : LRAFormula n k)
        (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams)
        (prep : TTCPreprocessor n k),
        SealedRun.expectedOperations F hbounded p prep ≤
          ENNReal.ofReal (C * ttcRuntimeRate (prep.run F hbounded) p) :=
  ⟨(10 : ℝ) ^ 54, by positivity, fun hn F hb p prep =>
    Tape.sealed_expectedOperations_le_runtimeRate hn F hb p prep⟩

#ttcModelClosureOfType ttc_theorem1_volume_accuracy
#ttcModelClosureOfType ttc_theorem3_expected_runtime
#print axioms ttc_theorem1_volume_accuracy
#print axioms ttc_theorem3_expected_runtime

end ttc
