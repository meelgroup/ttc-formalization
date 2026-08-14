import Ttc.Exec.CVGaussianSourceSharpCost

/-!
# Fixed-input source certificate for the uncapped Gaussian execution

This is the direct source-certificate packaging of the sharp expected-cost theorem.  It
uses the actual uncapped costed Gaussian law and a single global source cutoff downstream.
There is no per-phase deadline and no `1 / correctedNu` factor.  The only runtime premise
left is the deterministic sharp phase-sum comparison `hsum`.
-/

namespace Ttc.CVGaussianSourceSharpCertificate

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
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
open Ttc.CVSourceSharpIndependentCertificate
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.GenericCostedPhaseCertificate
open Ttc.CVGaussianSourceSharpCost
open scoped ENNReal Classical BigOperators

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- The concrete uncapped Gaussian streams produce the exact one-run certificate consumed
by the source cutoff capstone, conditional only on their established path accuracy and the
displayed deterministic phase-sum comparison. -/
theorem sourceOneRunCertificate_gaussianSharp
    (hn : 2 ≤ n) (k m : Nat)
    {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (q radius runtimeConstant eps : Real) (hq : 1 < q) (hR : 0 ≤ radius)
    (delta sigma shrink : Nat → Real)
    (hdelta : ∀ j, 0 < delta j) (hsigma : ∀ j, 0 < sigma j)
    (hshrink : ∀ j, shrink j ≠ 0)
    (hdeltan : ∀ j, delta j ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ j, j + 1 < m →
      delta j ≤ sigma j / (max 8 (2 * q) * Real.sqrt n))
    (hRsigma : ∀ j, j + 1 < m → radius ≤ q * sigma j * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ radius)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback tail : Nat → Measure (ScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    [∀ j, IsProbabilityMeasure (tail j)]
    [∀ j, IsProbabilityMeasure
      (ellGaussianProb K (delta j) ((sigma j) ^ 2))]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real) (eta : Real)
    (hop : SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
            hdelta hshrink steps retries fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
          hdelta hshrink steps retries fallback) tail)
      Prod.snd Prod.fst mu0 V m eta)
    (hpi : ∀ j, hop.pi j = ellGaussianProb K (delta j) ((sigma j) ^ 2))
    (hMtop : ∀ j, hop.warmConst j ≠ ⊤)
    (est : (Fin k → Nat → ScoreSeed n) → Real) (hest : Measurable est)
    {lo hi : Real}
    (hsum : (k : ENNReal) * ∑ j ∈ Finset.range m,
        gaussianActiveMeanEnvelope m hop.warmConst steps retries j ≤
      sourceOneRunQueryBudget runtimeConstant n radius eps)
    (haccuracy : 4 / 5 ≤
      (independentPathLaw k
        (stateScheduleFromSeed
          (activeReferenceTailSchedule m
            (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
              hdelta hshrink steps retries fallback) tail)) mu0).real
        {omega | est omega ∈ Icc lo hi}) :
    SourceOneRunCertificate
      (independentCostedLaw k
        (costedStateScheduleFromSeed
          (costedActiveReferenceTailSchedule m
            (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
              hdelta hshrink steps retries fallback) tail)) mu0)
      (independentQueryCost m) (independentValue est)
      runtimeConstant n radius eps lo hi := by
  let P := stateScheduleFromSeed
    (activeReferenceTailSchedule m
      (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
        hdelta hshrink steps retries fallback) tail)
  let Q := costedStateScheduleFromSeed
    (costedActiveReferenceTailSchedule m
      (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
        hdelta hshrink steps retries fallback) tail)
  apply sourceOneRunCertificate_of_independentCostedStreams
    P Q mu0 (gaussianActiveMeanEnvelope m hop.warmConst steps retries)
    _ _ est hest hsum haccuracy
  · intro i z
    apply map_snd_costedStateActiveReferenceTailSchedule m
      (warmFallbackSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
        hdelta hshrink steps retries fallback)
      (warmFallbackCostedSchedule K hK delta (fun j ↦ (sigma j) ^ 2) shrink
        hdelta hshrink steps retries fallback) tail
    intro j x
    exact map_snd_gaussianWarmFallbackCostedPhaseKernel hK (delta j)
      ((sigma j) ^ 2) (shrink j) (hdelta j) (hshrink j)
      (steps j) (retries j) (fallback j) x
  · intro j hj
    unfold gaussianActiveMeanEnvelope
    by_cases hactive : j + 1 < m
    · rw [if_pos hactive]
      exact phaseMean_costedActive_gaussian_le_of_operational hn m j hactive
        hK hKc hball q radius hq hR delta sigma shrink hdelta hsigma hshrink
        hdeltan hdeltaq hRsigma hKR steps retries fallback tail mu0 V eta hop hpi
        (hMtop j)
    · rw [if_neg hactive]
      exact le_of_eq
        (lintegral_stepMean_costedStateActiveReferenceTailSchedule_inactive m
          (warmFallbackCostedSchedule K hK delta (fun l ↦ (sigma l) ^ 2) shrink
            hdelta hshrink steps retries fallback) tail
          (stateMarginal Q mu0 j) j hactive)

#print axioms sourceOneRunCertificate_gaussianSharp

end Ttc.CVGaussianSourceSharpCertificate
