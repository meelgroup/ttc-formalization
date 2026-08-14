import Ttc.Exec.CVGaussianCappedCostEnvelope

/-! Expected-query volume-oracle assembly for capped Gaussian independent streams. -/

namespace Ttc.CVGaussianCappedExpectedVolume

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianCappedCostedSchedule
open Ttc.CVGaussianCappedCostEnvelope
open Ttc.CVSeedProjectedDependence
open Ttc.CVIndependentStreamGeneralizedCertificate
open Ttc.CVGeneralPolynomialCutoffCapstone
open Ttc.GenericCostedPhaseCertificate
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Complete public expected-query assembly once the scalar capped operation and the
corrected estimator accuracy have been established.  Active costs are derived from
`last_seed_warm`; the exact tail is charged zero. -/
noncomputable def expectedQueryVolumeAlgorithm_gaussianCapped_of_operational
    (hn : 2 ≤ n)
    (oneEnvelope : Ttc.CVAdaptive.VolumeInput n → Real)
    (k m : Ttc.CVAdaptive.VolumeInput n → Nat)
    (hK : ∀ a : Ttc.CVAdaptive.VolumeInput n, MeasurableSet a.1)
    (hKc : ∀ a : Ttc.CVAdaptive.VolumeInput n, Convex Real a.1)
    (hballAll : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      ball (0 : State n) 1 ⊆ a.1)
    (q R : Ttc.CVAdaptive.VolumeInput n → Real)
    (hq : ∀ a, 1 < q a) (hR : ∀ a, 0 ≤ R a)
    (delta sigma shrink : Ttc.CVAdaptive.VolumeInput n → Nat → Real)
    (hdelta : ∀ a j, 0 < delta a j)
    (hsigma : ∀ a j, 0 < sigma a j)
    (hshrink : ∀ a j, shrink a j ≠ 0)
    (hdeltan : ∀ a j, delta a j ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ a j, j + 1 < m a →
      delta a j ≤ sigma a j / (max 8 (2 * q a) * Real.sqrt n))
    (hRsigma : ∀ a j, j + 1 < m a →
      R a ≤ q a * sigma a j * Real.sqrt n)
    (hKR : ∀ a x, x ∈ a.1 → ‖x‖ ≤ R a)
    (steps : Ttc.CVAdaptive.VolumeInput n → Nat → Nat → Nat)
    (retries : Ttc.CVAdaptive.VolumeInput n → Nat → Nat)
    (fallback tail : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      Nat → Measure (ScoreSeed n))
    [∀ a j, IsProbabilityMeasure (fallback a j)]
    [∀ a j, IsProbabilityMeasure (tail a j)]
    [∀ a j, IsProbabilityMeasure
      (ellGaussianProb a.1 (delta a j) ((sigma a j) ^ 2))]
    (mu0 : ∀ a : Ttc.CVAdaptive.VolumeInput n, Measure (ScoreSeed n))
    [∀ a, IsProbabilityMeasure (mu0 a)]
    (Vscalar : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      Nat → (Nat → ScoreSeed n) → Real)
    (hop : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      SeedProjectedOperational
        (stateScheduleFromSeed
          (activeReferenceTailSchedule (m a)
            (warmFallbackSchedule a.1 (hK a) (delta a)
              (fun j ↦ (sigma a j) ^ 2) (shrink a)
              (hdelta a) (hshrink a) (steps a) (retries a) (fallback a))
            (tail a)))
        (activeReferenceTailSchedule (m a)
          (warmFallbackSchedule a.1 (hK a) (delta a)
            (fun j ↦ (sigma a j) ^ 2) (shrink a)
            (hdelta a) (hshrink a) (steps a) (retries a) (fallback a))
          (tail a))
        Prod.snd Prod.fst (mu0 a) (Vscalar a) (m a) a.2.1)
    (hpi : ∀ a j, (hop a).pi j =
      ellGaussianProb a.1 (delta a j) ((sigma a j) ^ 2))
    (hMtop : ∀ a j, (hop a).warmConst j ≠ ⊤)
    (est : ∀ a : Ttc.CVAdaptive.VolumeInput n,
      (Fin (k a) → Nat → ScoreSeed n) → Real)
    (hest : ∀ a, Measurable (est a))
    (henvelope : ∀ a,
      ((k a : Nat) : ENNReal) *
          ∑ j ∈ Finset.range (m a),
            (if j + 1 < m a then
              ENNReal.ofReal
                (Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope
                  ((hop a).warmConst j).toReal (steps a j) (retries a j))
             else 0) ≤
        ENNReal.ofReal (oneEnvelope a))
    (haccuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
      0 < eps → 0 < p → p < 1 → Convex Real K →
      ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
      4 / 5 ≤
        (Ttc.CVIndependentStreamDependence.independentPathLaw (k (K, eps, p))
          (stateScheduleFromSeed
            (activeReferenceTailSchedule (m (K, eps, p))
              (warmFallbackSchedule K (hK (K, eps, p)) (delta (K, eps, p))
                (fun j ↦ (sigma (K, eps, p) j) ^ 2) (shrink (K, eps, p))
                (hdelta (K, eps, p)) (hshrink (K, eps, p))
                (steps (K, eps, p)) (retries (K, eps, p))
                (fallback (K, eps, p))) (tail (K, eps, p))))
          (mu0 (K, eps, p))).real
          {omega | est (K, eps, p) omega ∈
            Icc ((1 - eps) * (volume K).toReal)
              ((1 + eps) * (volume K).toReal)}) :
    Ttc.ExpectedQueryVolumeAlgorithm n := by
  let phaseBound : ∀ a : Ttc.CVAdaptive.VolumeInput n, Nat → ENNReal :=
    fun a j ↦ if j + 1 < m a then
      ENNReal.ofReal
        (Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope
          ((hop a).warmConst j).toReal (steps a j) (retries a j))
      else 0
  let cert := generalizedPublicOneRunCertificates_activeReferenceTail oneEnvelope k m
    (fun a ↦ warmFallbackSchedule a.1 (hK a) (delta a)
      (fun j ↦ (sigma a j) ^ 2) (shrink a)
      (hdelta a) (hshrink a) (steps a) (retries a) (fallback a))
    (fun a ↦ warmFallbackCostedSchedule a.1 (hK a) (delta a)
      (fun j ↦ (sigma a j) ^ 2) (shrink a)
      (hdelta a) (hshrink a) (steps a) (retries a) (fallback a))
    tail mu0 phaseBound est
    (fun a j x ↦ map_snd_gaussianWarmFallbackCostedPhaseKernel (hK a)
      (delta a j) ((sigma a j) ^ 2) (shrink a j) (hdelta a j) (hshrink a j)
      (steps a j) (retries a j) (fallback a j) x)
    (by
      intro a j hj
      dsimp only [phaseBound]
      by_cases hactive : j + 1 < m a
      · rw [if_pos hactive]
        exact phaseMean_costedActive_gaussian_le_of_operational hn (m a) j hactive
          (hK a) (hKc a) (hballAll a)
          (q a) (R a) (hq a) (hR a) (delta a) (sigma a) (shrink a)
          (hdelta a) (hsigma a) (hshrink a) (hdeltan a) (hdeltaq a)
          (hRsigma a) (fun x hx ↦ hKR a x hx) (steps a) (retries a)
          (fallback a) (tail a) (mu0 a) (Vscalar a) a.2.1 (hop a) (hpi a)
          (hMtop a j)
      · rw [if_neg hactive]
        exact le_of_eq
          (lintegral_stepMean_costedStateActiveReferenceTailSchedule_inactive
          (m a)
          (warmFallbackCostedSchedule a.1 (hK a) (delta a)
            (fun l ↦ (sigma a l) ^ 2) (shrink a) (hdelta a) (hshrink a)
            (steps a) (retries a) (fallback a)) (tail a)
          (stateMarginal
            (costedStateScheduleFromSeed
              (costedActiveReferenceTailSchedule (m a)
                (warmFallbackCostedSchedule a.1 (hK a) (delta a)
                  (fun l ↦ (sigma a l) ^ 2) (shrink a) (hdelta a) (hshrink a)
                  (steps a) (retries a) (fallback a)) (tail a)))
            (mu0 a) j) j hactive))
    (by simpa only [phaseBound] using henvelope)
    hest haccuracy
  exact expectedQueryVolumeAlgorithm_activeReferenceTail oneEnvelope k m
    (fun a ↦ warmFallbackCostedSchedule a.1 (hK a) (delta a)
      (fun j ↦ (sigma a j) ^ 2) (shrink a)
      (hdelta a) (hshrink a) (steps a) (retries a) (fallback a))
    tail mu0 est cert

#print axioms expectedQueryVolumeAlgorithm_gaussianCapped_of_operational

end Ttc.CVGaussianCappedExpectedVolume
