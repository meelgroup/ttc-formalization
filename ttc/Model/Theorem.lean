import ttc.Model.Run
import ttc.Meta.ModelClosure
import ttc.Analysis.Tape.Theorem1
import ttc.Analysis.Tape.PublicRuntime

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

/-- Theorem 3 for the sealed program. Its expected tally is bounded by a
formula in the certified components and approximation parameters. In
particular no allowance for uncounted CV18 arithmetic is assumed. -/
theorem ttc_theorem3_expected_runtime {n k : ℕ} (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (p : ApproxParams)
    (prep : TTCPreprocessor n k) :
    SealedRun.expectedOperations F hbounded p prep ≤
      ENNReal.ofReal (ttcArithmeticBound (prep.run F hbounded) p) :=
  Tape.sealed_expectedOperations_le_arithmeticBound hn F hbounded p prep

#ttcModelClosureOfType ttc_theorem1_volume_accuracy
#ttcModelClosureOfType ttc_theorem3_expected_runtime
#print axioms ttc_theorem1_volume_accuracy
#print axioms ttc_theorem3_expected_runtime

end ttc
