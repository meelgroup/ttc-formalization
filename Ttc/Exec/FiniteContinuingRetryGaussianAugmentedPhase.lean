import Ttc.Exec.FiniteContinuingRetryGaussianPhaseKernel

/-!
# Gaussian retry phase retaining both estimator sample and next warm seed

The accepted candidate contains two logically different states: the rescaled point used by
the cooling-ratio estimator and the raw endpoint lying in the shrunken body, which starts
the next walk.  This phase kernel retains both.  On cutoff/no-hit it returns the incoming
pair unchanged.
-/

namespace Ttc.FiniteContinuingRetryGaussianAugmentedPhase

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianPhaseKernel
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
/-- `(sample used by the estimator, raw endpoint used as the next warm seed)`. -/
abbrev AugmentedState (n : Nat) := State n × State n

noncomputable def augmentedAcceptedOutput (c : Real) (z : CostedCoin n) :
    AugmentedState n :=
  (acceptedOutput c z, rejectedNext z)

theorem measurable_augmentedAcceptedOutput (c : Real) :
    Measurable (augmentedAcceptedOutput (n := n) c) :=
  (measurable_acceptedOutput c).prodMk measurable_rejectedNext

theorem augmentedAcceptedOutput_eq_graph (c : Real) (hc : c ≠ 0)
    (z : CostedCoin n) :
    augmentedAcceptedOutput c z = (acceptedOutput c z, c • acceptedOutput c z) := by
  unfold augmentedAcceptedOutput acceptedOutput rejectedNext
  simp [Ttc.CVCombinedContinuingAccept.combinedOutput,
    Ttc.CVCombinedContinuingAccept.combinedNext, hc]

/-- Any accepted pair law is exactly the graph lift of its score marginal. -/
theorem map_augmentedAcceptedOutput_eq_graph
    (c : Real) (hc : c ≠ 0) (mu : Measure (CostedCoin n)) :
    Measure.map (augmentedAcceptedOutput c) mu =
      Measure.map (fun y : State n ↦ (y, c • y))
        (Measure.map (acceptedOutput c) mu) := by
  rw [Measure.map_map (by fun_prop)
    (measurable_acceptedOutput c)]
  apply Measure.map_congr
  filter_upwards [] with z
  exact augmentedAcceptedOutput_eq_graph c hc z

theorem tvLe_map_augmentedAcceptedOutput_of_score
    (c : Real) (hc : c ≠ 0) {mu : Measure (CostedCoin n)}
    {tau : Measure (State n)} {eps : ENNReal}
    (h : Arlib.TVLe (Measure.map (acceptedOutput c) mu) tau eps) :
    Arlib.TVLe (Measure.map (augmentedAcceptedOutput c) mu)
      (Measure.map (fun y : State n ↦ (y, c • y)) tau) eps := by
  rw [map_augmentedAcceptedOutput_eq_graph c hc mu]
  exact h.map (by fun_prop)

/-- The incoming seed is the second coordinate; the full incoming pair is the unresolved
self-fallback. -/
def augmentedEmbedding (a : AugmentedState n) :
    RetryState (State n) (AugmentedState n) :=
  (a.2, false, a, 0)

theorem measurable_augmentedEmbedding :
    Measurable (augmentedEmbedding : AugmentedState n →
      RetryState (State n) (AugmentedState n)) := by
  unfold augmentedEmbedding
  fun_prop

noncomputable def augmentedGaussianRetrySchedule
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) :
    Nat → Kernel (RetryState (State n) (AugmentedState n))
      (RetryState (State n) (AugmentedState n)) :=
  retryStep
    (fun j ↦ combinedRoundCostedKernel K hK delta s hdelta (steps j))
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost

instance augmentedGaussianRetrySchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (j : Nat) :
    IsMarkovKernel
      (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps j) := by
  unfold augmentedGaussianRetrySchedule
  infer_instance

noncomputable def augmentedGaussianRetryStateKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    Kernel (AugmentedState n) (RetryState (State n) (AugmentedState n)) :=
  Kernel.comap
    (adaptiveKernel (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps) L)
    augmentedEmbedding measurable_augmentedEmbedding

instance augmentedGaussianRetryStateKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    IsMarkovKernel
      (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L) := by
  unfold augmentedGaussianRetryStateKernel
  infer_instance

theorem augmentedGaussianRetryStateKernel_apply
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (a : AugmentedState n) (L : Nat) :
    augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L a =
      Arlib.adaptiveMarginal
        (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps)
        (Measure.dirac (augmentedEmbedding a)) L := by
  unfold augmentedGaussianRetryStateKernel
  rw [Kernel.comap_apply]
  have h := sampleFromKernel_adaptiveKernel
    (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps)
    (Measure.dirac (augmentedEmbedding a)) L
  simpa only [sampleFromKernel, Measure.dirac_bind, Kernel.measurable] using h

noncomputable def augmentedPhaseCostOutput
    (z : RetryState (State n) (AugmentedState n)) : ENNReal × AugmentedState n :=
  (accumulatedCost z, output z)

theorem measurable_augmentedPhaseCostOutput :
    Measurable (augmentedPhaseCostOutput :
      RetryState (State n) (AugmentedState n) → ENNReal × AugmentedState n) :=
  measurable_accumulatedCost.prodMk measurable_output

noncomputable def augmentedGaussianFinitePhaseCostedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    Kernel (AugmentedState n) (ENNReal × AugmentedState n) :=
  Kernel.map
    (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L)
    augmentedPhaseCostOutput

instance augmentedGaussianFinitePhaseCostedKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    IsMarkovKernel
      (augmentedGaussianFinitePhaseCostedKernel K hK delta s c hdelta hc steps L) := by
  unfold augmentedGaussianFinitePhaseCostedKernel
  exact Kernel.IsMarkovKernel.map _ measurable_augmentedPhaseCostOutput

/-- Exact forget-cost law for the augmented phase state. -/
theorem map_snd_augmentedGaussianFinitePhaseCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (a : AugmentedState n) (L : Nat) :
    Measure.map Prod.snd
        (augmentedGaussianFinitePhaseCostedKernel K hK delta s c hdelta hc steps L a) =
      Measure.map output
        (Arlib.adaptiveMarginal
          (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps)
          (Measure.dirac (augmentedEmbedding a)) L) := by
  rw [augmentedGaussianFinitePhaseCostedKernel,
    Kernel.map_apply _ measurable_augmentedPhaseCostOutput,
    Measure.map_map measurable_snd measurable_augmentedPhaseCostOutput,
    augmentedGaussianRetryStateKernel_apply]
  rfl

/-- The recorded phase mean is exactly the accumulated number of traced membership
queries in the augmented retry state. -/
theorem lintegral_fst_augmentedGaussianFinitePhaseCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (a : AugmentedState n) (L : Nat) :
    ∫⁻ z, z.1
        ∂(augmentedGaussianFinitePhaseCostedKernel K hK delta s c hdelta hc steps L a) =
      ∫⁻ z, accumulatedCost z
        ∂(Arlib.adaptiveMarginal
          (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps)
          (Measure.dirac (augmentedEmbedding a)) L) := by
  rw [augmentedGaussianFinitePhaseCostedKernel,
    Kernel.map_apply _ measurable_augmentedPhaseCostOutput,
    lintegral_map measurable_fst measurable_augmentedPhaseCostOutput,
    augmentedGaussianRetryStateKernel_apply]
  rfl

/-- Law-level actual membership-query mean for one augmented phase. -/
noncomputable def augmentedPhaseQueryMean
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (rho : Measure (AugmentedState n)) : ENNReal :=
  ∫⁻ z, accumulatedCost z
    ∂sampleFromKernel
      (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L) rho

/-- Averaging the generic sequential `stepMean` against an arbitrary incoming probability
law gives exactly the actual accumulated traced-query mean. -/
theorem lintegral_stepMean_augmentedGaussianFinitePhaseCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (rho : Measure (AugmentedState n)) [IsProbabilityMeasure rho] :
    (∫⁻ a, Ttc.SequentialCost.stepMean
      (fun _ ↦ augmentedGaussianFinitePhaseCostedKernel
        K hK delta s c hdelta hc steps L) 0 a ∂rho) =
      augmentedPhaseQueryMean K hK delta s c hdelta hc steps L rho := by
  unfold Ttc.SequentialCost.stepMean augmentedGaussianFinitePhaseCostedKernel
  simp_rw [Kernel.map_apply _ measurable_augmentedPhaseCostOutput,
    lintegral_map measurable_fst measurable_augmentedPhaseCostOutput]
  change (∫⁻ a, ∫⁻ z, accumulatedCost z
      ∂(augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L a) ∂rho) = _
  rw [← Measure.lintegral_bind
    (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L).aemeasurable
    measurable_accumulatedCost.aemeasurable]
  rfl

#print axioms map_snd_augmentedGaussianFinitePhaseCostedKernel
#print axioms lintegral_fst_augmentedGaussianFinitePhaseCostedKernel
#print axioms lintegral_stepMean_augmentedGaussianFinitePhaseCostedKernel

end Ttc.FiniteContinuingRetryGaussianAugmentedPhase
