import Kr25Ssmxt.Analysis.CV18HitAndRunOracles
import Kr25Ssmxt.Analysis.ManuscriptRuntimeBounds
import Kr25Ssmxt.Analysis.ManuscriptRunMarginal

namespace Kr25Ssmxt

open MeasureTheory

/-!
# The public TTC theorems

The proved accuracy statement below is for the older `communityTTC` core. The
current manuscript's algorithm is `communityManuscriptTTC`, with a separate
rate-thinning loop, scaled intensity, volume clipping, and output normalization.
An exact finite expected-operation bound for the charged newer program is
proved below, including the corrected headline's explicit geometric monomial.
The charged-to-uncharged output marginal is proved. A Lean polylogarithmic
estimate for the imported CV18 scheduled factors remains open.

`Prior` exposes the remaining high-intensity Poissonized streaming theorem as a hypothesis.
The deterministic preprocessing, oracle contracts, empty case, lattice
comparison, measure normalization, and final error composition are proved in this project.
-/

/--
The older TTC program using the current arlib-community CV18 and finite-step
Hit-and-Run/KV97 implementations returns a probability law on single nonnegative estimates,
and its estimate is within relative error `ε` of the Lebesgue volume of the existentially
projected real solution set with probability at least `1 - δ`.  The two geometric-oracle
contracts are discharged in the proof rather than exposed as assumptions. This
statement does not yet establish manuscript Theorem 1, because its program and
its public high-intensity and `Prior` premises differ from the printed claim.

PAPER: sections/analysis.tex:314-326
-/
theorem ttc_volume_accuracy
    (hprior : Prior)
    {n k : Nat}
    (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (prep : TTCPreprocessor n k)
    (hregime :
      let D := prep.run F hbounded
      let b := (prep.choosePrecision D params).value
      D.componentCount = 0 ∨
        params.threshold D.componentCount / 4 ≤ (scaledLatticeVolume D b : Real)) :
    MeasureTheory.IsProbabilityMeasure (communityTTC hn F hbounded params prep) ∧
      (communityTTC hn F hbounded params prep).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr params.epsilon
              (MeasureTheory.volume (solutionSet F)).toReal} ≥
        1 - params.delta := by
  exact ttc_volume_accuracy_communityCV18_hitAndRun
    hprior hn F hbounded params prep hregime

/-- Corrected Theorem 3: the charged execution has exactly the manuscript TTC
output law and its expected arithmetic cost has the preprocessing term plus
the explicit `m n⁵ ρ² r_max (1+b+log⁺ R_max)` scale. -/
theorem ttc_theorem3_corrected_expected_runtime {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (preprocessingOperations : Nat) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    (communityManuscriptTTCWithCost hn F hbounded p prep
      preprocessingOperations 1).map Prod.fst =
        communityManuscriptTTC hn F hbounded p prep ∧
    (∫⁻ result, (result.2 : ENNReal) ∂
      communityManuscriptTTCWithCost hn F hbounded p prep
        preprocessingOperations 1) ≤
      preprocessingOperations + (D.componentCount : ENNReal) *
        ENNReal.ofReal (30 * (n : Real) ^ 5 *
          (TTCRuntime.theorem3RMax D : Real) *
          (TTCRuntime.theorem3Rho D) ^ 2 *
          TTCRuntime.theorem3PrecisionScale b
            (TTCRuntime.theorem3OuterRadiusMax D) *
          ((TTCRuntime.sampleCap p D.componentCount : Real) + 1) *
          (TTCRuntime.theorem3ParameterFactor hn D p + 1)) := by
  dsimp only
  exact ⟨community_manuscript_costed_output_fst hn F hbounded p prep
    preprocessingOperations 1,
    ttc_expected_runtime_theorem3_headline_scale hn F hbounded p prep
      preprocessingOperations⟩

#krModelClosureOfType ttc_volume_accuracy
#krModelClosureOfType ttc_theorem3_corrected_expected_runtime
#krSurplusIn Kr25Ssmxt.Model from ttc_volume_accuracy
  ttc_theorem3_corrected_expected_runtime
  StreamingCoreAccuracy communityManuscriptTTC
  TTCRuntime.deletionPassOperations TTCRuntime.rateThinningRoundOperations
  TTCRuntime.countThinningRoundOperations TTCRuntime.samplingAttemptOperations
  TTCRuntime.poissonDrawOperations TTCRuntime.appendCopyOperations
  manuscriptRateThinWithCost manuscriptCountThinWithCost

/-!
Both public statements are recursively sealed above.  `communityTTC` and every executable
adapter it unfolds are defined under `Model/`; `Analysis/` is used only to prove the two
statements.
-/

#print axioms ttc_volume_accuracy
#print axioms ttc_theorem3_corrected_expected_runtime

end Kr25Ssmxt
