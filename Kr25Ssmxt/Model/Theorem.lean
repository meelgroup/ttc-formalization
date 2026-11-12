import Kr25Ssmxt.Analysis.CommunityCV18VolumeProvider
import Kr25Ssmxt.Analysis.HitAndRunSamplingOracle
import Kr25Ssmxt.Analysis.RuntimeBounds
import Kr25Ssmxt.Analysis.GetPrecisionBound
import Kr25Ssmxt.Analysis.Theorem3ExplicitBound
import Kr25Ssmxt.Analysis.RunMarginal
import Kr25Ssmxt.Analysis.TheoremOneFinal

namespace Kr25Ssmxt

open MeasureTheory

/-!
# The public TTC theorems

Both statements concern `ttc`, the TTC algorithm printed in the
current paper (Algorithm 1), run with the concrete arlib-community CV18 volume
oracle (clipped as in the paper) and the normalized Hit-and-Run/KV97 sampler.

Where the definitions are:
* `Model/Program.lean` — `ttcPseudocode F params O`: Algorithm 1's control flow (loops, thinning,
  Poisson draw, output `Est`) with its subroutines `O` left open.
* `Model/Run.lean` — the concrete subroutines (`GetPrecision` via the Chebyshev LP,
  `ComputeVolume` = CV18 + clipping, `GenerateSamples` = Hit-and-Run + KV97 rounding +
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
    (ttc hn F hbounded params prep).real
        {estimate | (estimate : Real) ∈
          Arlib.relErr params.epsilon
            (MeasureTheory.volume (solutionSet F)).toReal} ≥
      1 - params.delta := by
  exact community_ttc_volume_accuracy hn F hbounded params prep

/-- Corrected Theorem 3: the charged execution has exactly the paper TTC
output law and its expected arithmetic cost has the preprocessing term plus
the explicit `m n⁵ ρ² r_max (2 + log₁₀⁺ γ + log₁₀⁺ (1 / minᵢ γᵢ) + log⁺ R_max)`
scale, where `γ` is the radius required by `getprec` at `ε / 96`.  The bound
depends on the input only: the precision `b` chosen by `getprec` is bounded
by `1 + log₁₀⁺ γ + log₁₀⁺ (1 / minᵢ γᵢ)`. -/
theorem ttc_theorem3_corrected_expected_runtime {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    (ttcWithCost hn F hbounded p prep
      preprocessingOperations 1).map Prod.fst =
        ttc hn F hbounded p prep ∧
    (∫⁻ result, (result.2 : ENNReal) ∂
      ttcWithCost hn F hbounded p prep
        preprocessingOperations 1) ≤
      preprocessingOperations + (D.componentCount : ENNReal) *
        ENNReal.ofReal (30 * (n : Real) ^ 5 *
          (TTCRuntime.theorem3RMax D : Real) *
          (TTCRuntime.theorem3Rho D) ^ 2 *
          TTCRuntime.theorem3InputScale D p *
          ((TTCRuntime.sampleCap p D.componentCount : Real) + 1) *
          (TTCRuntime.theorem3ParameterFactor D p + 1)) := by
  dsimp only
  exact ⟨community_costed_output_fst hn F hbounded p prep
    preprocessingOperations 1,
    ttc_expected_runtime_theorem3_explicit hn F hbounded p prep
      preprocessingOperations⟩

#krModelClosureOfType ttc_theorem1_volume_accuracy
#krModelClosureOfType ttc_theorem3_corrected_expected_runtime
#krSurplusIn Kr25Ssmxt.Model from ttc_theorem1_volume_accuracy
  ttc_theorem3_corrected_expected_runtime
  ttc
  TTCRuntime.deletionPassOperations TTCRuntime.rateThinningRoundOperations
  TTCRuntime.countThinningRoundOperations TTCRuntime.samplingAttemptOperations
  TTCRuntime.poissonDrawOperations TTCRuntime.appendCopyOperations
  ttcPseudocode.firstLoopWithCost ttcPseudocode.secondLoopWithCost

/-!
Both public statements are recursively sealed above.  `ttc` and every
executable adapter it unfolds are defined under `Model/`; `Analysis/` is used only to prove the two
statements.
-/

#print axioms ttc_theorem1_volume_accuracy
#print axioms ttc_theorem3_corrected_expected_runtime

end Kr25Ssmxt
