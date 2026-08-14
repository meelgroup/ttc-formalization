import Ttc.Exec.CVGaussianScoreAwareMeanBudget
import Ttc.Exec.CVSourceSharpIndependentCertificate

/-!
# External-accuracy packaging for the literal score-aware Gaussian estimator

The operational proof is run at the explicit inner accuracy `eps / 4`.  The concrete
mean/clipping budget proved in `CVGaussianScoreAwareMeanBudget` fits inside the public
accuracy `eps`.  This file also fixes both telescope endpoints to their literal Gaussian
chain values, so the target is the actual volume.
-/

namespace Ttc.CVGaussianScoreAwareExternalAccuracy

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling Arlib.MarkovChains
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianOperationalAccuracy
open Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVIndependentStreamMoments Ttc.CVIndependentStreamDependence
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVSourceSharpIndependentCertificate
open Ttc.GenericCostedPhaseCertificate
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The literal raw Gaussian estimator, run at the corrected inner accuracy. -/
noncomputable def scoreAwareLiteralEstimator
    {Seed : Type*} [MeasurableSpace Seed]
    (m : Nat) (eps : Real) (sigmaSq : Nat → Real) (K : Set (State n)) :
    (Fin (correctedRuntimeSamples m (correctedInnerAccuracy eps)) →
      Nat → State n × Seed) → Real :=
  fun omega => chain m sigmaSq K 0 *
    phaseProduct
      (fun j => streamAverage
        (k := correctedRuntimeSamples m (correctedInnerAccuracy eps))
        (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)) m omega

theorem measurable_scoreAwareLiteralEstimator
    {Seed : Type*} [MeasurableSpace Seed]
    {m : Nat} {eps : Real} {sigmaSq : Nat → Real} {K : Set (State n)}
    (hK : MeasurableSet K) :
    Measurable (scoreAwareLiteralEstimator (Seed := Seed) m eps sigmaSq K) := by
  have hWm : ∀ j, Measurable
      (streamAverage
        (k := correctedRuntimeSamples m (correctedInnerAccuracy eps))
        (positiveScalarPhaseFamily (Seed := Seed) m sigmaSq K j)) :=
    fun j => measurable_streamAverage (measurable_positiveScalarPhaseFamily hK j)
  unfold scoreAwareLiteralEstimator phaseProduct
  fun_prop

/-- Valid-branch `4/5` accuracy for the literal estimator at the requested (external)
accuracy.  The initial Gaussian normalizer and the final volume endpoint are no longer
hypotheses. -/
theorem scoreAware_operational_accuracy_volume
    {Seed : Type*} [MeasurableSpace Seed]
    {m : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {eps R : Real} {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    (hop : IndependentStreamOperational
      (correctedRuntimeSamples m (correctedInnerAccuracy eps))
      (stateScheduleFromSeed Q) Q Prod.snd mu0
      (clippedPositiveEmpiricalFamily m (correctedInnerAccuracy eps)
        Q mu0 sigmaSq K) m (correctedInnerAccuracy eps))
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m
        (correctedRuntimeSamples m (correctedInnerAccuracy eps))
        (correctedInnerAccuracy eps)
        (phaseMomentSlackSeven m sigmaSq K C)
        (phaseScoreTransportBoundSqSeven R sigmaSq)) j)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) = coolLaw m sigmaSq K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7)
    (hexact : ∀ i,
      ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
          ∂(coolLaw m sigmaSq K i) ≤
        C i * (∫ x, phaseScore m sigmaSq (interior K) i x
          ∂(coolLaw m sigmaSq K i)) ^ 2)
    (hm : 0 < m) :
    4 / 5 ≤
      (independentPathLaw
        (correctedRuntimeSamples m (correctedInnerAccuracy eps))
        (stateScheduleFromSeed Q) mu0).real
        {omega | scoreAwareLiteralEstimator (Seed := Seed) m eps sigmaSq K omega ∈
          Ttc.relErr eps (volume K).toReal} := by
  have hi0 : 0 < correctedInnerAccuracy eps := by
    unfold correctedInnerAccuracy
    positivity
  have hi1 : correctedInnerAccuracy eps ≤ 1 := by
    unfold correctedInnerAccuracy
    linarith
  have hinner := scoreAware_operational_accuracy_literal
    (eps := correctedInnerAccuracy eps) hop hmixError hi0 hi1 hsigma hK hKc hball hfin
    hKR htarget hC0 hC7 hexact hm
    (chain m sigmaSq K 0) (volume K).toReal
    (chain_pos hsigma hball hfin 0).le (volume K).toReal_nonneg rfl
    (chain_end m sigmaSq K).symm
  have hrequested := scoreAwareAccuracyRequested_inner_le (m := m) heps heps1
  exact hinner.trans (measureReal_mono
    (fun _ h => Ttc.CV.relErr_mono hrequested (volume K).toReal_nonneg h)
    (measure_ne_top _ _))

/-- Source-one-run certificate for the same literal estimator.  At this abstraction
boundary the only cost assumptions are the costed kernel's forgetful identity, its
per-phase expected-cost envelope, and the single sharp phase-sum comparison. -/
theorem sourceOneRunCertificate_scoreAwareLiteral
    {Seed : Type} [MeasurableSpace Seed]
    {m : Nat} {Q : Nat → Kernel Seed (State n × Seed)}
    [∀ i, IsMarkovKernel (Q i)]
    (Qcost : Nat → Kernel (State n × Seed) (ENNReal × (State n × Seed)))
    [∀ i, IsMarkovKernel (Qcost i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    (phaseBound : Nat → ENNReal)
    (hforget : ∀ i x,
      Measure.map Prod.snd (Qcost i x) = stateScheduleFromSeed Q i x)
    (hphase : ∀ i, i < m →
      (∫⁻ x, Ttc.SequentialCost.stepMean Qcost i x
        ∂stateMarginal Qcost mu0 i) ≤ phaseBound i)
    {runtimeConstant eps R : Real}
    (hsum :
      (correctedRuntimeSamples m (correctedInnerAccuracy eps) : ENNReal) *
          ∑ i ∈ Finset.range m, phaseBound i ≤
        Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
          runtimeConstant n R eps)
    {sigmaSq : Nat → Real} {K : Set (State n)} {C : Nat → Real}
    (hop : IndependentStreamOperational
      (correctedRuntimeSamples m (correctedInnerAccuracy eps))
      (stateScheduleFromSeed Q) Q Prod.snd mu0
      (clippedPositiveEmpiricalFamily m (correctedInnerAccuracy eps)
        Q mu0 sigmaSq K) m (correctedInnerAccuracy eps))
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError m
      (scoreAwareMixError m
        (correctedRuntimeSamples m (correctedInnerAccuracy eps))
        (correctedInnerAccuracy eps)
        (phaseMomentSlackSeven m sigmaSq K C)
        (phaseScoreTransportBoundSqSeven R sigmaSq)) j)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsigma : ∀ j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) = coolLaw m sigmaSq K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7)
    (hexact : ∀ i,
      ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2
          ∂(coolLaw m sigmaSq K i) ≤
        C i * (∫ x, phaseScore m sigmaSq (interior K) i x
          ∂(coolLaw m sigmaSq K i)) ^ 2)
    (hm : 0 < m) :
    Ttc.CVSourcePolynomialCutoffCapstone.SourceOneRunCertificate
      (Ttc.CVIndependentStreamGeneralizedCertificate.independentCostedLaw
        (correctedRuntimeSamples m (correctedInnerAccuracy eps)) Qcost mu0)
      (Ttc.CVIndependentStreamGeneralizedCertificate.independentQueryCost m)
      (Ttc.CVIndependentStreamGeneralizedCertificate.independentValue
        (scoreAwareLiteralEstimator (Seed := Seed) m eps sigmaSq K))
      runtimeConstant n R eps
      ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal) := by
  apply sourceOneRunCertificate_of_independentCostedStreams
    (stateScheduleFromSeed Q) Qcost mu0 phaseBound hforget hphase
    (scoreAwareLiteralEstimator (Seed := Seed) m eps sigmaSq K)
    (measurable_scoreAwareLiteralEstimator hK) hsum
  simpa only [Ttc.relErr] using
    scoreAware_operational_accuracy_volume hop hmixError heps heps1 hsigma hK hKc
      hball hfin hKR htarget hC0 hC7 hexact hm

#print axioms scoreAwareAccuracyRequested_inner_le
#print axioms scoreAware_operational_accuracy_volume
#print axioms measurable_scoreAwareLiteralEstimator
#print axioms sourceOneRunCertificate_scoreAwareLiteral

end Ttc.CVGaussianScoreAwareExternalAccuracy
