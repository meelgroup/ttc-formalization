import Ttc.Exec.CVFiniteContinuingPhaseSchedule
import Ttc.Exec.CVCombinedContinuingRetryDistributionalTV

/-! Law-level bridge from arbitrary incoming measures to the finite retry phase schedule. -/

namespace Ttc.CVFiniteContinuingPhaseDistributional

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianPhaseKernel
open Ttc.CVFiniteContinuingPhaseSchedule
open Ttc.CVCombinedContinuingRetryDistributionalTV
open Ttc.CVCombinedContinuingRetryPhaseTV
open scoped ENNReal Classical Pointwise

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem sampleFromKernel_map (Q : Kernel A B) [IsMarkovKernel Q]
    {D : Type*} [MeasurableSpace D] (f : B → D) (hf : Measurable f)
    (rho : Measure A) [IsProbabilityMeasure rho] :
    sampleFromKernel (Kernel.map Q f) rho =
      Measure.map f (sampleFromKernel Q rho) := by
  unfold sampleFromKernel
  rw [← Kernel.deterministic_comp_eq_map hf Q, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map hf]

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

theorem sampleFrom_gaussianRetryStateKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (fallback : State n) (L : Nat) :
    sampleFromKernel
      (gaussianRetryStateKernel K hK delta s c hdelta hc steps fallback L) rho =
      phaseMarginalOf K hK delta s c hdelta hc steps rho fallback L := by
  letI : IsProbabilityMeasure (Measure.map (initialRetryState fallback) rho) :=
    Measure.isProbabilityMeasure_map
      (measurable_initialRetryState fallback).aemeasurable
  unfold gaussianRetryStateKernel sampleFromKernel
  rw [Arlib.MarkovChains.bind_comap]
  have h := sampleFromKernel_adaptiveKernel
    (gaussianRetrySchedule K hK delta s c hdelta hc steps)
    (Measure.map (initialRetryState fallback) rho) L
  change _ = Arlib.adaptiveMarginal
    (gaussianRetrySchedule K hK delta s c hdelta hc steps)
    (Measure.map (initialRetryState fallback) rho) L at h
  unfold sampleFromKernel at h
  rw [h]
  rfl

/-- The declared cutoff state schedule really is the query-cutoff output of the
distributional retry marginal, not a mixture of pointwise-normalized phase laws. -/
theorem sampleFrom_finiteRetryStateSchedule
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (fallback : Nat → State n)
    (retries : Nat → Nat) (queryCutoff : Nat → ENNReal)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (i : Nat) :
    sampleFromKernel
      (finiteRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps fallback retries queryCutoff i) rho =
      Measure.map (queryCutoffOutput (fallback i) (queryCutoff i))
        (phaseMarginalOf K hK (delta i) (sigmaSq i) (shrink i)
          (hdelta i) (hshrink i) (retrySteps i) rho (fallback i) (retries i)) := by
  unfold finiteRetryStateSchedule finiteRetryCostedSchedule
  rw [sampleFromKernel_map _ Prod.snd measurable_snd rho]
  unfold gaussianCutoffPhaseCostedKernel
  rw [sampleFromKernel_map _ (cutoffPhaseCostOutput (fallback i) (queryCutoff i))
    (measurable_cutoffPhaseCostOutput (fallback i) (queryCutoff i)) rho]
  rw [Measure.map_map measurable_snd
    (measurable_cutoffPhaseCostOutput (fallback i) (queryCutoff i))]
  change Measure.map (queryCutoffOutput (fallback i) (queryCutoff i))
      (sampleFromKernel
        (gaussianRetryStateKernel K hK (delta i) (sigmaSq i) (shrink i)
          (hdelta i) (hshrink i) (retrySteps i) (fallback i) (retries i)) rho) = _
  rw [sampleFrom_gaussianRetryStateKernel]

/-- Query-cutoff transfer in exactly the distributional-mixing shape required by
`DirectSequentialOperational.distributional_mixing`. -/
theorem tvLe_sampleFrom_finiteRetryStateSchedule
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (fallback : Nat → State n)
    (retries : Nat → Nat) (queryCutoff : Nat → ENNReal)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (i : Nat)
    (target : Measure (State n)) {etaQuery epsPhase : ENNReal}
    (hcut0 : queryCutoff i ≠ 0) (hcuttop : queryCutoff i ≠ ⊤)
    (hmean : (∫⁻ z, Ttc.FiniteContinuingRetry.accumulatedCost z
      ∂phaseMarginalOf K hK (delta i) (sigmaSq i) (shrink i)
        (hdelta i) (hshrink i) (retrySteps i) rho (fallback i) (retries i)) /
          queryCutoff i ≤ etaQuery)
    (hphase : TVLe
      (Measure.map (Ttc.FiniteContinuingRetryDecomposition.cutoffOutput (fallback i))
        (phaseMarginalOf K hK (delta i) (sigmaSq i) (shrink i)
          (hdelta i) (hshrink i) (retrySteps i) rho (fallback i) (retries i)))
      target epsPhase) :
    TVLe
      (sampleFromKernel
        (finiteRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps fallback retries queryCutoff i) rho)
      target (etaQuery + epsPhase) := by
  letI : IsProbabilityMeasure
      (phaseMarginalOf K hK (delta i) (sigmaSq i) (shrink i)
        (hdelta i) (hshrink i) (retrySteps i) rho (fallback i) (retries i)) := by
    unfold phaseMarginalOf
    infer_instance
  rw [sampleFrom_finiteRetryStateSchedule hK delta sigmaSq shrink hdelta hshrink
    retrySteps fallback retries queryCutoff rho i]
  exact tvLe_queryCutoffOutput_target _ (fallback i) target hcut0 hcuttop hmean hphase

#print axioms sampleFrom_gaussianRetryStateKernel
#print axioms sampleFrom_finiteRetryStateSchedule
#print axioms tvLe_sampleFrom_finiteRetryStateSchedule

end Ttc.CVFiniteContinuingPhaseDistributional
