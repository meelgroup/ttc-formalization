import Ttc.Exec.CVGaussianScoreAwareExternalAccuracy
import Ttc.Exec.CVGaussianSourceSharpCertificate

/-!
# Sharp Gaussian source certificate with literal score-aware accuracy

This combines the literal `eps / 4` accuracy theorem with the uncapped Gaussian sharp-cost
certificate.  The costed/uncosted forgetful identity and every per-phase expected-cost
bound are discharged by the concrete Gaussian APIs.  The sole remaining runtime premise
is the deterministic sum comparison `hsum`.
-/

namespace Ttc.CVGaussianScoreAwareSourceCertificate

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianCappedCostedSchedule
open Ttc.CVGaussianCappedCostEnvelope
open Ttc.CVGaussianAdaptiveAcceptedWarm
open Ttc.CVSeedProjectedDependence
open Ttc.CVIndependentStreamDependence
open Ttc.CVIndependentStreamGeneralizedCertificate
open Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVGaussianScoreAwareExternalAccuracy
open Ttc.CVGaussianSourceSharpCost
open Ttc.CVGaussianSourceSharpCertificate
open Ttc.CVSourcePolynomialCutoffCapstone
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- The concrete uncapped Gaussian one-run certificate, with literal estimator and actual
volume target.  On the runtime side only `hsum` remains. -/
theorem sourceOneRunCertificate_gaussianSharp_scoreAwareLiteral
    (hn : 2 ≤ n) (m : Nat)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (q radius runtimeConstant eps : Real) (hq : 1 < q) (hR : 0 ≤ radius)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (delta sigma shrink : Nat → Real)
    (hdelta : ∀ j, 0 < delta j) (hsigma : ∀ j, 0 < sigma j)
    (hshrink : ∀ j, shrink j ≠ 0)
    (hdeltan : ∀ j, delta j ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ j, j + 1 < m →
      delta j ≤ sigma j / (max 8 (2 * q) * Real.sqrt n))
    (hRsigma : ∀ j, j + 1 < m → radius ≤ q * sigma j * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ radius)
    (hfin : volume K ≠ ⊤)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback tail : Nat → Measure (ScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    [∀ j, IsProbabilityMeasure (tail j)]
    [∀ j, IsProbabilityMeasure
      (ellGaussianProb K (delta j) ((sigma j) ^ 2))]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (Vcost : Nat → (Nat → ScoreSeed n) → Real) (etaCost : Real)
    (hopCost : SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
            hdelta hshrink steps retries fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
          hdelta hshrink steps retries fallback) tail)
      Prod.snd Prod.fst mu0 Vcost m etaCost)
    (hpiCost : ∀ j, hopCost.pi j = ellGaussianProb K (delta j) ((sigma j) ^ 2))
    (hMtop : ∀ j, hopCost.warmConst j ≠ ⊤)
    (C : Nat → Real)
    (hopAccuracy : IndependentStreamOperational
      (correctedRuntimeSamples m (correctedInnerAccuracy eps))
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
            hdelta hshrink steps retries fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
          hdelta hshrink steps retries fallback) tail)
      Prod.snd mu0
      (clippedPositiveEmpiricalFamily m (correctedInnerAccuracy eps)
        (activeReferenceTailSchedule m
          (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
            hdelta hshrink steps retries fallback) tail)
        mu0 (fun j ↦ (sigma j) ^ 2) K)
      m (correctedInnerAccuracy eps))
    (hmixError : ∀ j, hopAccuracy.mixError j = activeReferenceMixError m
      (scoreAwareMixError m
        (correctedRuntimeSamples m (correctedInnerAccuracy eps))
        (correctedInnerAccuracy eps)
        (phaseMomentSlackSeven m (fun j ↦ (sigma j) ^ 2) K C)
        (phaseScoreTransportBoundSqSeven radius (fun j ↦ (sigma j) ^ 2))) j)
    (htarget : ∀ i, Measure.map Prod.fst (hopAccuracy.tau i) =
      coolLaw m (fun j ↦ (sigma j) ^ 2) K i)
    (hC0 : ∀ i, 0 ≤ C i) (hC7 : ∀ i, C i < 7)
    (hexact : ∀ i,
      ∫ x, phaseScore m (fun j ↦ (sigma j) ^ 2) (interior K) i x ^ 2
          ∂(coolLaw m (fun j ↦ (sigma j) ^ 2) K i) ≤
        C i * (∫ x, phaseScore m (fun j ↦ (sigma j) ^ 2) (interior K) i x
          ∂(coolLaw m (fun j ↦ (sigma j) ^ 2) K i)) ^ 2)
    (hm : 0 < m)
    (hsum :
      (correctedRuntimeSamples m (correctedInnerAccuracy eps) : ENNReal) *
        ∑ j ∈ Finset.range m,
          gaussianActiveMeanEnvelope m hopCost.warmConst steps retries j ≤
      sourceOneRunQueryBudget runtimeConstant n radius eps) :
    SourceOneRunCertificate
      (independentCostedLaw
        (correctedRuntimeSamples m (correctedInnerAccuracy eps))
        (costedStateScheduleFromSeed
          (costedActiveReferenceTailSchedule m
            (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
              hdelta hshrink steps retries fallback) tail)) mu0)
      (independentQueryCost m)
      (independentValue
        (scoreAwareLiteralEstimator (Seed := State n) m eps
          (fun j ↦ (sigma j) ^ 2) K))
      runtimeConstant n radius eps
      ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal) := by
  have hsigmaSq : ∀ j, 0 < (sigma j) ^ 2 := fun j => sq_pos_of_pos (hsigma j)
  have hKRset : K ⊆ closedBall (0 : State n) radius := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hKR x hx
  apply sourceOneRunCertificate_gaussianSharp hn
    (correctedRuntimeSamples m (correctedInnerAccuracy eps)) m hK hKc hball
    q radius runtimeConstant eps hq hR delta sigma shrink hdelta hsigma hshrink
    hdeltan hdeltaq hRsigma hKR steps retries fallback tail mu0 Vcost etaCost
    hopCost hpiCost hMtop
    (scoreAwareLiteralEstimator (Seed := State n) m eps
      (fun j ↦ (sigma j) ^ 2) K)
    (measurable_scoreAwareLiteralEstimator hK) hsum
  simpa only [Ttc.relErr] using
    scoreAware_operational_accuracy_volume hopAccuracy hmixError heps heps1
      hsigmaSq hK hKc hball hfin hKRset htarget hC0 hC7 hexact hm

#print axioms sourceOneRunCertificate_gaussianSharp_scoreAwareLiteral

end Ttc.CVGaussianScoreAwareSourceCertificate
