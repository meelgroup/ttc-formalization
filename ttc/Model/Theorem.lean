import ttc.Analysis.CommunityCV18VolumeProvider
import ttc.Analysis.HitAndRunSamplingOracle
import ttc.Analysis.RuntimeBounds
import ttc.Analysis.GetPrecisionBound
import ttc.Analysis.Theorem3ExplicitBound
import ttc.Analysis.RunMarginal
import ttc.Analysis.TheoremOneFinal
import ttc.Analysis.TTCSimulation

namespace ttc

open MeasureTheory

/-!
# The public TTC theorems

Both statements concern `ttc`, the TTC algorithm printed in the
current paper (Algorithm 1), run with the concrete arlib-community CV18 volume
oracle and the normalized Hit-and-Run/KV97 sampler.

Where the definitions are:
* `Model/Program.lean` — `ttcPseudocode F params O`: Algorithm 1's control flow (`p ← Thresh`,
  the rate check `k ← ⌈log₂ (t p / Thresh)⌉`, thinning, Poisson draw, the halving loop,
  output `Est = |X| / (p · 10^{bn})`) with its subroutines `O` left open.
* `Model/Run.lean` — the concrete subroutines (`GetPrecision` via the Chebyshev LP,
  `ComputeVolume` = CV18, `GenerateSamples` = Hit-and-Run + KV97 rounding +
  rejection), and `ttc := ttcPseudocode F params (those subroutines)`, the object of Theorem 1.
  `ttcWithCost` is the same run with operation counts, the object of Theorem 3.

* Theorem 1: the output is an `ε`-relative estimate of the volume of the projected
  solution set with probability at least `1 - δ`. No prior-work hypothesis is assumed.
* Theorem 3 (corrected): the charged execution has exactly the same output law, and its
  expected operation count has the explicit input-only scale
  `m n⁵ ρ² r_max (2 + log₁₀⁺ γ + log₁₀⁺ (1 / minᵢ γᵢ) + log⁺ R_max)`.
  Every constant is explicit in `n`, `m`, `ρ`, `r_max`, `R_max`, `ε` and `δ`
  (`Model/Prelude.lean`); CV18's scheduled logarithmic factors enter through arlib-community's
  bound `figureOneScheduledLogEnvelope_le`.
-/

/-- Theorem 1 for the current paper TTC program: with the concrete
CV18 and normalized Hit-and-Run/KV97 oracles, the output is within relative
error `ε` of the Lebesgue volume of the existentially projected solution set
with probability at least `1 - δ`.  It has no prior-work hypothesis and no
regime premise.

PAPER: sections/analysis.tex:314-326
-/
theorem ttc_theorem1_volume_accuracy
    {n k : Nat}
    (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (prep : TTCPreprocessor n k) :
    Pr[estimate ← ttc hn F hbounded params prep;
      (estimate : Real) ∈
        Arlib.relErr params.epsilon (MeasureTheory.volume (solutionSet F)).toReal] ≥
      1 - params.delta := by
  rw [ttc_eq_ttcRef]
  exact community_ttc_volume_accuracy hn F hbounded params prep

/-- Corrected Theorem 3.

* **Same algorithm.** For every measurable set `S` of outputs, the charged run's output lands in
  `S` with the same probability as `ttc`'s. Equivalently, the output distribution of
  `ttcWithCost`, with its cost discarded, is that of `ttc`, so the cost bound is about the
  algorithm of Theorem 1.
* **Expected cost.** The expected operation count is at most the preprocessing cost plus
  `m · 30 n⁵ · r_max · ρ² · (⌈Thresh⌉ + 1) · polylogFactors / ε²`, which depends on the input
  only. -/
theorem ttc_theorem3_expected_runtime {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    (∀ S : Set NNReal, MeasurableSet S →
      Pr[result ← ttcWithCost hn F hbounded p prep preprocessingOperations 1; result.1 ∈ S] =
        Pr[estimate ← ttc hn F hbounded p prep; estimate ∈ S]) ∧
    Exp[result ← ttcWithCost hn F hbounded p prep preprocessingOperations 1;
      (result.2 : ENNReal)] ≤
      preprocessingOperations + (D.componentCount : ENNReal) *
        ENNReal.ofReal (30 * (n : Real) ^ 5 *
          (TTCRuntime.RMax D : Real) *
          (TTCRuntime.Rho D) ^ 2 *
          ((TTCRuntime.ThresholdCap p D.componentCount : Real) + 1) *
          TTCRuntime.polylogFactors D p / p.epsilon ^ 2) := by
  dsimp only
  rw [ttcWithCost_eq_ttcRefWithCost, ttc_eq_ttcRef]
  refine ⟨fun S hS => ?_, ttc_expected_runtime_theorem3_explicit hn F hbounded p prep
    preprocessingOperations⟩
  rw [← community_costed_output_fst hn F hbounded p prep preprocessingOperations 1,
    measureReal_def, measureReal_def, Set.setOf_mem_eq, Measure.map_apply measurable_fst hS]
  rfl

#krModelClosureOfType ttc_theorem1_volume_accuracy
#krModelClosureOfType ttc_theorem3_expected_runtime
#krSurplusIn ttc.Model from ttc_theorem1_volume_accuracy
  ttc_theorem3_expected_runtime
  ttc
  TTCState.deletionCost TTCRuntime.rateThinningRoundOperations
  TTCRuntime.countThinningRoundOperations PolytopeData.samplingAttemptCost
  TTCRuntime.poissonDrawOperations TTCRuntime.appendCopyOperations
  ttcPseudocode.rateCheckWithCost ttcPseudocode.secondLoopWithCost

/-!
Both public statements are recursively sealed above.  `ttc` and every
executable adapter it unfolds are defined under `Model/`; `Analysis/` is used only to prove the two
statements.
-/

#print axioms ttc_theorem1_volume_accuracy
#print axioms ttc_theorem3_expected_runtime

end ttc
