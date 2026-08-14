import Ttc.Exec.CVGaussianWarmFallbackPhaseKernel
import Ttc.Exec.CVGaussianWarmFallbackOperational
import Ttc.Exec.CVConcreteAugmentedRetryCutoffBudget
import Ttc.Exec.CVIndependentStreamGeneralizedCertificate

/-!
# Cost-recording Gaussian warm-fallback phases

The independent fallback performs no membership query.  We therefore retain the finite
retry state's accumulated query count, then apply `randomFallbackKernel` only to its
output coordinate.  This is the missing costed companion of
`gaussianWarmFallbackPhaseKernel`.
-/

namespace Ttc.CVGaussianWarmFallbackCostedPhaseKernel

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.GenericCostedPhaseCertificate
open Ttc.CVIndependentStreamGeneralizedCertificate
open scoped ENNReal Classical

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- Attach the already accumulated retry cost to the independently postprocessed output. -/
noncomputable def randomFallbackCostedKernel
    (fallback : Measure F) [IsProbabilityMeasure fallback] :
    Kernel (RetryState E F) (ENNReal × F) :=
  Kernel.map
    (Kernel.compProd Kernel.id
      (Kernel.prodMkLeft (RetryState E F) (randomFallbackKernel fallback)))
    (fun q ↦ (accumulatedCost q.1, q.2))

instance randomFallbackCostedKernel.isMarkovKernel
    (fallback : Measure F) [IsProbabilityMeasure fallback] :
    IsMarkovKernel (randomFallbackCostedKernel (E := E) fallback) := by
  unfold randomFallbackCostedKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_accumulatedCost.comp measurable_fst |>.prodMk
    measurable_snd)

/-- Erasing cost gives exactly the existing independent random-fallback kernel. -/
theorem map_snd_randomFallbackCostedKernel
    (fallback : Measure F) [IsProbabilityMeasure fallback] (z : RetryState E F) :
    Measure.map Prod.snd (randomFallbackCostedKernel fallback z) =
      randomFallbackKernel fallback z := by
  have hout : Measurable (fun q : RetryState E F × F ↦
      (accumulatedCost q.1, q.2)) :=
    (measurable_accumulatedCost.comp measurable_fst).prodMk measurable_snd
  rw [randomFallbackCostedKernel, Kernel.map_apply _ hout,
    Measure.map_map measurable_snd hout]
  change (Kernel.compProd Kernel.id
      (Kernel.prodMkLeft (RetryState E F) (randomFallbackKernel fallback))).snd z = _
  rw [Kernel.snd_compProd_prodMkLeft, Kernel.comp_id]

/-- The fallback draw adds zero membership queries: the recorded mean is the cost already
stored in the retry state. -/
theorem lintegral_fst_randomFallbackCostedKernel
    (fallback : Measure F) [IsProbabilityMeasure fallback] (z : RetryState E F) :
    ∫⁻ q, q.1 ∂randomFallbackCostedKernel fallback z = accumulatedCost z := by
  have hout : Measurable (fun q : RetryState E F × F ↦
      (accumulatedCost q.1, q.2)) :=
    (measurable_accumulatedCost.comp measurable_fst).prodMk measurable_snd
  rw [randomFallbackCostedKernel, Kernel.map_apply _ hout,
    lintegral_map measurable_fst hout]
  change (∫⁻ q : RetryState E F × F, (accumulatedCost ∘ Prod.fst) q
      ∂Kernel.compProd Kernel.id
        (Kernel.prodMkLeft (RetryState E F) (randomFallbackKernel fallback)) z) = _
  rw [Kernel.lintegral_compProd Kernel.id _ z
      (measurable_accumulatedCost.comp measurable_fst)]
  simp_rw [Function.comp_apply]
  simp_rw [Kernel.prodMkLeft_apply]
  simp_rw [lintegral_const]
  have huniv : ∀ b : RetryState E F,
      randomFallbackKernel fallback b Set.univ = 1 := fun b ↦ by
    letI : IsProbabilityMeasure (randomFallbackKernel fallback b) := inferInstance
    exact measure_univ
  simp_rw [huniv, mul_one]
  rw [Kernel.id_apply, lintegral_dirac' z measurable_accumulatedCost]

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Seed-indexed costed Gaussian finite-retry phase with an independent warm fallback. -/
noncomputable def gaussianWarmFallbackCostedPhaseKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback] :
    Kernel (State n) (ENNReal × ScoreSeed n) :=
  randomFallbackCostedKernel fallback ∘ₖ
    Kernel.comap
      (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L)
      (seedEmbedding c) (measurable_seedEmbedding c)

instance gaussianWarmFallbackCostedPhaseKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback] :
    IsMarkovKernel
      (gaussianWarmFallbackCostedPhaseKernel K hK delta s c hdelta hc steps L fallback) := by
  unfold gaussianWarmFallbackCostedPhaseKernel
  infer_instance

/-- The costed kernel is a literal refinement of `gaussianWarmFallbackPhaseKernel`. -/
theorem map_snd_gaussianWarmFallbackCostedPhaseKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (x : State n) :
    Measure.map Prod.snd
        (gaussianWarmFallbackCostedPhaseKernel K hK delta s c hdelta hc steps L fallback x) =
      gaussianWarmFallbackPhaseKernel K hK delta s c hdelta hc steps L fallback x := by
  change (gaussianWarmFallbackCostedPhaseKernel K hK delta s c hdelta hc steps L
    fallback).snd x = _
  rw [gaussianWarmFallbackCostedPhaseKernel, Kernel.snd_comp]
  have hpost : (randomFallbackCostedKernel (E := State n) fallback).snd =
      randomFallbackKernel fallback := by
    apply Kernel.ext
    intro z
    rw [Kernel.snd_apply]
    exact map_snd_randomFallbackCostedKernel fallback z
  rw [hpost]
  rfl

/-- Pointwise recorded query mean: precisely the accumulated finite-retry cost. -/
theorem lintegral_fst_gaussianWarmFallbackCostedPhaseKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (x : State n) :
    ∫⁻ q, q.1
        ∂gaussianWarmFallbackCostedPhaseKernel K hK delta s c hdelta hc steps L fallback x =
      ∫⁻ z, accumulatedCost z
        ∂augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L
          (seedEmbedding c x) := by
  rw [gaussianWarmFallbackCostedPhaseKernel,
    Kernel.lintegral_comp _ _ _ measurable_fst]
  simp_rw [lintegral_fst_randomFallbackCostedKernel fallback]
  rw [Kernel.comap_apply]

/-- Averaging the costed phase over an incoming seed law is exactly the already-defined
`warmFallbackPhaseQueryMean`. -/
theorem lintegral_stepMean_gaussianWarmFallbackCostedPhaseKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho] :
    (∫⁻ x, Ttc.SequentialCost.stepMean
      (fun _ ↦ costedStateKernelFromSeed
        (gaussianWarmFallbackCostedPhaseKernel K hK delta s c hdelta hc
          steps L fallback)) 0 x ∂rho) =
      warmFallbackPhaseQueryMean K hK delta s c hdelta hc steps L
        (Measure.map Prod.snd rho) := by
  simp_rw [Ttc.SequentialCost.stepMean,
    costedStateKernelFromSeed, Kernel.comap_apply,
    lintegral_fst_gaussianWarmFallbackCostedPhaseKernel hK delta s c hdelta hc
      steps L fallback]
  unfold warmFallbackPhaseQueryMean augmentedPhaseQueryMean
    Ttc.CVSequentialPhaseSampler.sampleFromKernel
  rw [Measure.lintegral_bind
    (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L).aemeasurable
    measurable_accumulatedCost.aemeasurable,
    Measure.map_map (measurable_seedEmbedding c) measurable_snd,
    lintegral_map
      (measurable_accumulatedCost.lintegral_kernel (κ :=
        augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L))
      ((measurable_seedEmbedding c).comp measurable_snd)]
  rfl

/-- Source geometric upper bound, now attached to the literal costed random-fallback
kernel.  The fallback itself adds no query, so the bound is unchanged. -/
theorem lintegral_stepMean_gaussianWarmFallbackCostedPhaseKernel_le_referenceEnvelope
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {q delta sigma R c : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hc : c ≠ 0)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho]
    (pi : Measure (State n)) [IsProbabilityMeasure pi]
    (hpi : pi = Arlib.MarkovChains.ellGaussianProb K delta (sigma ^ 2))
    {M : Real} (hM : 0 ≤ M)
    (hwarm : ∀ j, j < L → IsWarm (ENNReal.ofReal M)
      (Ttc.FiniteContinuingRetryExpectedCost.runningCurrent
        (Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf K hK delta
          (sigma ^ 2) c hdelta hc steps
          (Measure.map (seedEmbedding c) (Measure.map Prod.snd rho)) j)) pi) :
    (∫⁻ x, Ttc.SequentialCost.stepMean
      (fun _ ↦ costedStateKernelFromSeed
        (gaussianWarmFallbackCostedPhaseKernel K hK delta (sigma ^ 2) c hdelta hc
          steps L fallback)) 0 x ∂rho) ≤
      ENNReal.ofReal (retryReferenceMeanEnvelope M steps L) := by
  rw [lintegral_stepMean_gaussianWarmFallbackCostedPhaseKernel hK delta
    (sigma ^ 2) c hdelta hc steps L fallback rho]
  letI : IsProbabilityMeasure (Measure.map Prod.snd rho) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact warmFallbackPhaseQueryMean_le_referenceEnvelope hn hK hKc hball hq hdelta
    hsigma hc hdeltan hdeltaq hR hRsigma hKR steps (Measure.map Prod.snd rho) pi hpi
    hM L hwarm

/-- Time-inhomogeneous seed-indexed costed family. -/
noncomputable def warmFallbackCostedSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) := fun i ↦
  gaussianWarmFallbackCostedPhaseKernel K hK (delta i) (sigmaSq i) (shrink i)
    (hdelta i) (hshrink i) (retrySteps i) (retries i) (fallback i)

instance warmFallbackCostedSchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (warmFallbackCostedSchedule K hK delta sigmaSq shrink hdelta
      hshrink retrySteps retries fallback i) := by
  unfold warmFallbackCostedSchedule
  infer_instance

/-- Exact cost erasure for the lifted augmented-state schedule, ready for
`independentCostedLaw`. -/
theorem map_snd_costedStateWarmFallbackSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) (z : ScoreSeed n) :
    Measure.map Prod.snd
        (costedStateScheduleFromSeed
          (warmFallbackCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries fallback) i z) =
      stateScheduleFromSeed
        (Ttc.CVGaussianWarmFallbackOperational.warmFallbackSchedule K hK delta sigmaSq
          shrink hdelta hshrink retrySteps retries fallback) i z := by
  apply map_snd_costedStateScheduleFromSeed
  intro j x
  exact map_snd_gaussianWarmFallbackCostedPhaseKernel hK (delta j) (sigmaSq j)
    (shrink j) (hdelta j) (hshrink j) (retrySteps j) (retries j) (fallback j) x

/-- The full random-fallback family is a generic sequential cost refinement.  Its sole
runtime input is the actual incoming-marginal scalar phase-query bound. -/
theorem costedStateWarmFallbackRefinement
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat → ENNReal)
    (hphase : ∀ i, i < m →
      (∫⁻ x, Ttc.SequentialCost.stepMean
        (costedStateScheduleFromSeed
          (warmFallbackCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries fallback)) i x
        ∂stateMarginal
          (costedStateScheduleFromSeed
            (warmFallbackCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries fallback)) mu0 i) ≤ phaseBound i) :
    Refinement
      (stateScheduleFromSeed
        (Ttc.CVGaussianWarmFallbackOperational.warmFallbackSchedule K hK delta sigmaSq
          shrink hdelta hshrink retrySteps retries fallback))
      (costedStateScheduleFromSeed
        (warmFallbackCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries fallback)) mu0 m phaseBound where
  forgetCost := map_snd_costedStateWarmFallbackSchedule K hK delta sigmaSq shrink
    hdelta hshrink retrySteps retries fallback
  phaseMean := hphase

/-- Concrete product-law erasure: `k` independent costed random-fallback executions are
exactly the `independentPathLaw` used by corrected CV accuracy. -/
theorem map_independentStatePaths_warmFallbackCostedLaw
    (k : Nat) (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0] :
    Measure.map independentStatePaths
        (independentCostedLaw k
          (costedStateScheduleFromSeed
            (warmFallbackCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries fallback)) mu0) =
      Ttc.CVIndependentStreamDependence.independentPathLaw k
        (stateScheduleFromSeed
          (Ttc.CVGaussianWarmFallbackOperational.warmFallbackSchedule K hK delta sigmaSq
            shrink hdelta hshrink retrySteps retries fallback)) mu0 := by
  exact map_independentStatePaths_independentCostedLaw k _ _ mu0
    (map_snd_costedStateWarmFallbackSchedule K hK delta sigmaSq shrink hdelta
      hshrink retrySteps retries fallback)

/-- Honest independent-stream query accounting for the concrete costed warm-fallback
schedule.  A scalar incoming-marginal phase bound is charged exactly `k` times. -/
theorem lintegral_independentWarmFallbackQueryCost_le_phaseBounds
    (k m : Nat) (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (phaseBound : Nat → ENNReal)
    (hphase : ∀ i, i < m →
      (∫⁻ x, Ttc.SequentialCost.stepMean
        (costedStateScheduleFromSeed
          (warmFallbackCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries fallback)) i x
        ∂stateMarginal
          (costedStateScheduleFromSeed
            (warmFallbackCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries fallback)) mu0 i) ≤ phaseBound i) :
    (∫⁻ omega, independentQueryCost m omega
      ∂independentCostedLaw k
        (costedStateScheduleFromSeed
          (warmFallbackCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries fallback)) mu0) ≤
      (k : ENNReal) * ∑ i ∈ Finset.range m, phaseBound i := by
  exact lintegral_independentQueryCost_le_phaseBounds k m _ mu0 phaseBound hphase

#print axioms map_snd_randomFallbackCostedKernel
#print axioms lintegral_fst_randomFallbackCostedKernel
#print axioms map_snd_gaussianWarmFallbackCostedPhaseKernel
#print axioms lintegral_stepMean_gaussianWarmFallbackCostedPhaseKernel
#print axioms lintegral_stepMean_gaussianWarmFallbackCostedPhaseKernel_le_referenceEnvelope
#print axioms map_snd_costedStateWarmFallbackSchedule
#print axioms costedStateWarmFallbackRefinement
#print axioms map_independentStatePaths_warmFallbackCostedLaw
#print axioms lintegral_independentWarmFallbackQueryCost_le_phaseBounds

end Ttc.CVGaussianWarmFallbackCostedPhaseKernel
