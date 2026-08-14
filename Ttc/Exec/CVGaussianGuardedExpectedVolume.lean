import Ttc.Exec.CVGuardedGeneralizedPublic
import Ttc.Exec.CVGaussianCappedExpectedVolume
import Ttc.Exec.CVGaussianAdaptiveIndependentOperational
import Ttc.Exec.CVGaussianWarmFallbackScoreMoment

/-! Literal guarded public oracle for capped costed Gaussian streams. -/

namespace Ttc.CVGaussianGuardedExpectedVolume

open MeasureTheory ProbabilityTheory Metric Set
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVGaussianCappedCostedSchedule
open Ttc.CVIndependentStreamGeneralizedCertificate
open Ttc.CVGuardedGeneralizedPublic
open Ttc.CVGaussianCappedCostEnvelope
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVSeedProjectedDependence
open Ttc.GenericCostedPhaseCertificate
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def gaussianClosedRawLaw
    (k m : VolumeInput n → Nat)
    (delta sigmaSq shrink : VolumeInput n → Nat → Real)
    (hdelta : ∀ a i, 0 < delta a i) (hshrink : ∀ a i, shrink a i ≠ 0)
    (steps : VolumeInput n → Nat → Nat → Nat)
    (retries : VolumeInput n → Nat → Nat)
    (fallback tail : ∀ a : VolumeInput n, Nat → Measure (ScoreSeed n))
    [∀ a i, IsProbabilityMeasure (fallback a i)]
    [∀ a i, IsProbabilityMeasure (tail a i)]
    (mu0 : ∀ a : VolumeInput n, Measure (ScoreSeed n))
    [∀ a, IsProbabilityMeasure (mu0 a)]
    (a : VolumeInput n) (h : ClosedAdmissible a) :
    Measure (IndependentCostedPath (k a) (ScoreSeed n)) :=
  independentCostedLaw (k a)
    (costedStateScheduleFromSeed
      (costedActiveReferenceTailSchedule (m a)
        (warmFallbackCostedSchedule a.1 h.2.2.2.2.1.measurableSet
          (delta a) (sigmaSq a) (shrink a) (hdelta a) (hshrink a)
          (steps a) (retries a) (fallback a)) (tail a))) (mu0 a)

instance gaussianClosedRawLaw.isProbabilityMeasure
    (k m : VolumeInput n → Nat)
    (delta sigmaSq shrink : VolumeInput n → Nat → Real)
    (hdelta : ∀ a i, 0 < delta a i) (hshrink : ∀ a i, shrink a i ≠ 0)
    (steps : VolumeInput n → Nat → Nat → Nat)
    (retries : VolumeInput n → Nat → Nat)
    (fallback tail : ∀ a : VolumeInput n, Nat → Measure (ScoreSeed n))
    [∀ a i, IsProbabilityMeasure (fallback a i)]
    [∀ a i, IsProbabilityMeasure (tail a i)]
    (mu0 : ∀ a : VolumeInput n, Measure (ScoreSeed n))
    [∀ a, IsProbabilityMeasure (mu0 a)] (a : VolumeInput n)
    (h : ClosedAdmissible a) :
    IsProbabilityMeasure (gaussianClosedRawLaw k m delta sigmaSq shrink hdelta
      hshrink steps retries fallback tail mu0 a h) := by
  unfold gaussianClosedRawLaw
  infer_instance

noncomputable def gaussianClosedRawCost
    (k m : VolumeInput n → Nat) (a : VolumeInput n) (_h : ClosedAdmissible a) :
    IndependentCostedPath (k a) (ScoreSeed n) → ENNReal :=
  independentQueryCost (m a)

noncomputable def gaussianClosedRawValue
    (k : VolumeInput n → Nat)
    (est : ∀ a, ClosedAdmissible a →
      (Fin (k a) → Nat → ScoreSeed n) → Real)
    (a : VolumeInput n) (h : ClosedAdmissible a) :
    IndependentCostedPath (k a) (ScoreSeed n) → Real :=
  independentValue (est a h)

/-- Expected-cost premise of the guarded Gaussian constructor, derived from the scalar
operational warmth and the explicit sum of active retry envelopes. -/
theorem gaussianClosedRaw_expected_le_of_operational
    (hn : 2 ≤ n) (a : VolumeInput n) (h : ClosedAdmissible a)
    (rawEnvelope : Real) (k m : Nat)
    (q R : Real) (hq : 1 < q) (hR : 0 ≤ R)
    (delta sigma shrink : Nat → Real)
    (hdelta : ∀ j, 0 < delta j) (hsigma : ∀ j, 0 < sigma j)
    (hshrink : ∀ j, shrink j ≠ 0)
    (hdeltan : ∀ j, delta j ≤ 1 / (2 * (n : Real)))
    (hdeltaq : ∀ j, j + 1 < m →
      delta j ≤ sigma j / (max 8 (2 * q) * Real.sqrt n))
    (hRsigma : ∀ j, j + 1 < m → R ≤ q * sigma j * Real.sqrt n)
    (hKR : ∀ x ∈ a.1, ‖x‖ ≤ R)
    (steps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback tail : Nat → Measure (ScoreSeed n))
    [∀ j, IsProbabilityMeasure (fallback j)]
    [∀ j, IsProbabilityMeasure (tail j)]
    [∀ j, IsProbabilityMeasure (Arlib.MarkovChains.ellGaussianProb
      a.1 (delta j) ((sigma j) ^ 2))]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (Vscalar : Nat → (Nat → ScoreSeed n) → Real)
    (hop : SeedProjectedOperational
      (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (warmFallbackSchedule a.1 h.2.2.2.2.1.measurableSet delta
            (fun j ↦ (sigma j) ^ 2) shrink hdelta hshrink steps retries fallback) tail))
      (activeReferenceTailSchedule m
        (warmFallbackSchedule a.1 h.2.2.2.2.1.measurableSet delta
          (fun j ↦ (sigma j) ^ 2) shrink hdelta hshrink steps retries fallback) tail)
      Prod.snd Prod.fst mu0 Vscalar m a.2.1)
    (hpi : ∀ j, hop.pi j = Arlib.MarkovChains.ellGaussianProb
      a.1 (delta j) ((sigma j) ^ 2))
    (hMtop : ∀ j, hop.warmConst j ≠ ⊤)
    (henvelope : (k : ENNReal) *
        ∑ j ∈ Finset.range m,
          (if j + 1 < m then
            ENNReal.ofReal
              (Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope
                (hop.warmConst j).toReal (steps j) (retries j)) else 0) ≤
      ENNReal.ofReal rawEnvelope) :
    (∫⁻ omega, independentQueryCost m omega
      ∂independentCostedLaw k
        (costedStateScheduleFromSeed
          (costedActiveReferenceTailSchedule m
            (warmFallbackCostedSchedule a.1 h.2.2.2.2.1.measurableSet delta
              (fun j ↦ (sigma j) ^ 2) shrink hdelta hshrink steps retries fallback)
            tail)) mu0) ≤ ENNReal.ofReal rawEnvelope := by
  let phaseBound : Nat → ENNReal := fun j ↦ if j + 1 < m then
    ENNReal.ofReal
      (Ttc.CVConcreteAugmentedRetryCutoffBudget.retryReferenceMeanEnvelope
        (hop.warmConst j).toReal (steps j) (retries j)) else 0
  refine (lintegral_independentQueryCost_le_phaseBounds k m
    (costedStateScheduleFromSeed
      (costedActiveReferenceTailSchedule m
        (warmFallbackCostedSchedule a.1 h.2.2.2.2.1.measurableSet delta
          (fun j ↦ (sigma j) ^ 2) shrink hdelta hshrink steps retries fallback) tail))
    mu0 phaseBound ?_).trans ?_
  · intro j hj
    dsimp only [phaseBound]
    by_cases hactive : j + 1 < m
    · rw [if_pos hactive]
      exact phaseMean_costedActive_gaussian_le_of_operational hn m j hactive
        h.2.2.2.2.1.measurableSet h.2.2.2.1
        (Metric.ball_subset_closedBall.trans h.2.2.2.2.2.2.2.1)
        q R hq hR delta sigma shrink hdelta hsigma hshrink hdeltan hdeltaq
        hRsigma hKR steps retries fallback tail mu0 Vscalar a.2.1 hop hpi (hMtop j)
    · rw [if_neg hactive]
      exact le_of_eq
        (lintegral_stepMean_costedStateActiveReferenceTailSchedule_inactive m
          (warmFallbackCostedSchedule a.1 h.2.2.2.2.1.measurableSet delta
            (fun l ↦ (sigma l) ^ 2) shrink hdelta hshrink steps retries fallback)
          tail
          (stateMarginal
            (costedStateScheduleFromSeed
              (costedActiveReferenceTailSchedule m
                (warmFallbackCostedSchedule a.1 h.2.2.2.2.1.measurableSet delta
                  (fun l ↦ (sigma l) ^ 2) shrink hdelta hshrink steps retries fallback)
                tail)) mu0 j) j hactive)
  · simpa only [phaseBound] using henvelope

/-- Literal Gaussian specialization of the guarded public constructor.  There are no
universal body hypotheses: the raw costed schedule is elaborated only under
`ClosedAdmissible`; the other branch is the zero-cost Dirac law from the guard.

The two remaining premises are exact and local.  `hexpected` is supplied by
`phaseMean_costedActive_gaussian_le_of_operational` plus the summed envelope, while
`haccuracy` is the independent-stream corrected-estimator theorem. -/
noncomputable def guardedExpectedQueryVolumeAlgorithm_gaussianCapped
    (hn : 1 ≤ n)
    (rawEnvelope : VolumeInput n → Real)
    (k m : VolumeInput n → Nat)
    (delta sigmaSq shrink : VolumeInput n → Nat → Real)
    (hdelta : ∀ a i, 0 < delta a i) (hshrink : ∀ a i, shrink a i ≠ 0)
    (steps : VolumeInput n → Nat → Nat → Nat)
    (retries : VolumeInput n → Nat → Nat)
    (fallback tail : ∀ a : VolumeInput n, Nat → Measure (ScoreSeed n))
    [∀ a i, IsProbabilityMeasure (fallback a i)]
    [∀ a i, IsProbabilityMeasure (tail a i)]
    (mu0 : ∀ a : VolumeInput n, Measure (ScoreSeed n))
    [∀ a, IsProbabilityMeasure (mu0 a)]
    (est : ∀ a, ClosedAdmissible a →
      (Fin (k a) → Nat → ScoreSeed n) → Real)
    (hest : ∀ a h, Measurable (est a h))
    (hexpected : ∀ a h,
      (∫⁻ omega, gaussianClosedRawCost k m a h omega
        ∂gaussianClosedRawLaw k m delta sigmaSq shrink hdelta hshrink steps
          retries fallback tail mu0 a h) ≤ ENNReal.ofReal (rawEnvelope a))
    (haccuracy : ∀ a (h : ClosedAdmissible a),
      4 / 5 ≤
        (gaussianClosedRawLaw k m delta sigmaSq shrink hdelta hshrink steps
          retries fallback tail mu0 a h).real
          {omega | gaussianClosedRawValue k est a h omega ∈
            Icc ((1 - a.2.1) * (volume a.1).toReal)
              ((1 + a.2.1) * (volume a.1).toReal)}) :
    Ttc.ExpectedQueryVolumeAlgorithm n :=
  guardedExpectedQueryVolumeAlgorithm
    (fun a ↦ IndependentCostedPath (k a) (ScoreSeed n)) hn rawEnvelope
    (gaussianClosedRawLaw k m delta sigmaSq shrink hdelta hshrink steps retries
      fallback tail mu0)
    (gaussianClosedRawCost k m)
    (gaussianClosedRawValue k est)
    (fun _a _h ↦ measurable_independentQueryCost _)
    (fun _a _h ↦ measurable_independentValue (hest _a _h))
    hexpected haccuracy

#print axioms gaussianClosedRawLaw
#print axioms gaussianClosedRaw_expected_le_of_operational
#print axioms guardedExpectedQueryVolumeAlgorithm_gaussianCapped

end Ttc.CVGaussianGuardedExpectedVolume
