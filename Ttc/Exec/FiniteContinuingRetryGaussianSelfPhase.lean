import Ttc.Exec.FiniteContinuingRetrySelfFallback
import Ttc.Exec.FiniteContinuingRetryGaussianPhaseKernel

/-! State-indexed Gaussian retry phase with the incoming point as unresolved fallback. -/

namespace Ttc.FiniteContinuingRetryGaussianSelfPhase

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianPhaseKernel
open Ttc.FiniteContinuingRetrySelfFallback
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Full retry-state kernel initialized by `x ↦ (x,false,x,0)`. -/
noncomputable def gaussianSelfRetryStateKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    Kernel (State n) (RetryState (State n) (State n)) :=
  Kernel.comap
    (adaptiveKernel (gaussianRetrySchedule K hK delta s c hdelta hc steps) L)
    selfEmbedding measurable_selfEmbedding

instance gaussianSelfRetryStateKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    IsMarkovKernel (gaussianSelfRetryStateKernel K hK delta s c hdelta hc steps L) := by
  unfold gaussianSelfRetryStateKernel
  infer_instance

/-- Binding the self-fallback state kernel against an arbitrary incoming law gives the
law-level self marginal exactly. -/
theorem sampleFrom_gaussianSelfRetryStateKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (L : Nat) :
    sampleFromKernel (gaussianSelfRetryStateKernel K hK delta s c hdelta hc steps L) rho =
      selfMarginal
        (fun j ↦ combinedRoundCostedKernel K hK delta s hdelta (steps j))
        (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
        rejectedNext (acceptedOutput c) measurable_rejectedNext (measurable_acceptedOutput c)
        roundQueryCost measurable_roundQueryCost rho L := by
  letI : IsProbabilityMeasure (Measure.map selfEmbedding rho) :=
    Measure.isProbabilityMeasure_map measurable_selfEmbedding.aemeasurable
  unfold gaussianSelfRetryStateKernel sampleFromKernel
  rw [Arlib.MarkovChains.bind_comap]
  have h := sampleFromKernel_adaptiveKernel
    (gaussianRetrySchedule K hK delta s c hdelta hc steps)
    (Measure.map selfEmbedding rho) L
  unfold sampleFromKernel at h
  rw [h]
  rfl

/-- Cost together with the stored output; on unresolved executions this output is the
incoming point. -/
noncomputable def selfPhaseCostOutput
    (z : RetryState (State n) (State n)) : ENNReal × State n :=
  (accumulatedCost z, output z)

theorem measurable_selfPhaseCostOutput :
    Measurable (selfPhaseCostOutput : RetryState (State n) (State n) →
      ENNReal × State n) :=
  measurable_accumulatedCost.prodMk measurable_output

noncomputable def gaussianSelfFinitePhaseCostedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    Kernel (State n) (ENNReal × State n) :=
  Kernel.map (gaussianSelfRetryStateKernel K hK delta s c hdelta hc steps L)
    selfPhaseCostOutput

instance gaussianSelfFinitePhaseCostedKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat) :
    IsMarkovKernel
      (gaussianSelfFinitePhaseCostedKernel K hK delta s c hdelta hc steps L) := by
  unfold gaussianSelfFinitePhaseCostedKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_selfPhaseCostOutput (n := n))

theorem map_snd_gaussianSelfFinitePhaseCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (x : State n) :
    Measure.map Prod.snd
      (gaussianSelfFinitePhaseCostedKernel K hK delta s c hdelta hc steps L x) =
      Measure.map output
        (gaussianSelfRetryStateKernel K hK delta s c hdelta hc steps L x) := by
  unfold gaussianSelfFinitePhaseCostedKernel
  rw [Kernel.map_apply _ measurable_selfPhaseCostOutput,
    Measure.map_map measurable_snd measurable_selfPhaseCostOutput]
  rfl

theorem stepMean_gaussianSelfFinitePhaseCostedKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (x : State n) :
    Ttc.SequentialCost.stepMean
      (fun _ ↦ gaussianSelfFinitePhaseCostedKernel K hK delta s c hdelta hc steps L) 0 x =
      ∫⁻ z, accumulatedCost z
        ∂(gaussianSelfRetryStateKernel K hK delta s c hdelta hc steps L x) := by
  unfold Ttc.SequentialCost.stepMean gaussianSelfFinitePhaseCostedKernel
  rw [Kernel.map_apply _ measurable_selfPhaseCostOutput,
    lintegral_map measurable_fst measurable_selfPhaseCostOutput]
  rfl

#print axioms sampleFrom_gaussianSelfRetryStateKernel
#print axioms map_snd_gaussianSelfFinitePhaseCostedKernel
#print axioms stepMean_gaussianSelfFinitePhaseCostedKernel

end Ttc.FiniteContinuingRetryGaussianSelfPhase
