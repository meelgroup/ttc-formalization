import Ttc.Exec.CVFiniteContinuingSelfSchedule
import Ttc.Exec.CVSourceOneRunFromCostedPhases

/-!
# Cost capstone for finite continuing self-fallback phases

This file identifies the averaged `SequentialCost.stepMean` used by the public
source cutoff with the expected accumulated cost stored by the actual finite retry
state.  Consequently the remaining phase-cost premise speaks directly about recorded
membership queries, rather than an opaque costed-kernel field.
-/

namespace Ttc.CVFiniteContinuingSelfCostCapstone

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler
open Ttc.CVSourceOneRunFromCostedPhases
open Ttc.CVFiniteContinuingSelfSchedule
open Ttc.CostedPathwisePhaseLumping
open Ttc.CostedStatefulSpeedyPhases
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianSelfPhase
open Ttc.FiniteContinuingRetrySelfFallback
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev StatePath (n : Nat) := Nat → State n

/-- The expected number of recorded membership queries made by self-fallback phase `i`
when its incoming state has law `rho`. -/
noncomputable def selfRetryPhaseQueryMean
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) (i : Nat) : ENNReal :=
  ∫⁻ z, accumulatedCost z
    ∂selfMarginal
      (fun j ↦ combinedRoundCostedKernel K hK (delta i) (sigmaSq i)
        (hdelta i) (retrySteps i j))
      (costedCombinedAccept K (shrink i) (sigmaSq i))
      (measurableSet_costedCombinedAccept hK (hshrink i))
      rejectedNext (acceptedOutput (shrink i)) measurable_rejectedNext
      (measurable_acceptedOutput (shrink i)) roundQueryCost
      measurable_roundQueryCost rho (retries i)

/-- Exact identification of the phase mean used by `SequentialCost` with the recorded
query count accumulated by the operational retry state. -/
theorem lintegral_stepMean_selfRetryCostedSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (i : Nat) :
    (∫⁻ x, Ttc.SequentialCost.stepMean
      (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries) i x ∂rho) =
      selfRetryPhaseQueryMean K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries rho i := by
  unfold Ttc.SequentialCost.stepMean selfRetryCostedSchedule
  unfold gaussianSelfFinitePhaseCostedKernel
  simp_rw [Kernel.map_apply _ measurable_selfPhaseCostOutput,
    lintegral_map measurable_fst measurable_selfPhaseCostOutput]
  change (∫⁻ x, ∫⁻ z, accumulatedCost z
      ∂(gaussianSelfRetryStateKernel K hK (delta i) (sigmaSq i) (shrink i)
        (hdelta i) (hshrink i) (retrySteps i) (retries i) x) ∂rho) = _
  rw [← Measure.lintegral_bind
    (gaussianSelfRetryStateKernel K hK (delta i) (sigmaSq i) (shrink i)
      (hdelta i) (hshrink i) (retrySteps i) (retries i)).aemeasurable
    measurable_accumulatedCost.aemeasurable]
  change ∫⁻ z, accumulatedCost z
      ∂sampleFromKernel
        (gaussianSelfRetryStateKernel K hK (delta i) (sigmaSq i) (shrink i)
          (hdelta i) (hshrink i) (retrySteps i) (retries i)) rho = _
  rw [sampleFrom_gaussianSelfRetryStateKernel]
  rfl

/-- The operational refinement follows from bounds on the actual accumulated query means.
This is the narrow analytic seam left for the retry-cost estimate. -/
theorem selfRetryCostedPhaseRefinement_of_queryMeans
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat → ENNReal)
    (hquery : ∀ i, i < m →
      selfRetryPhaseQueryMean K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries
        (costedPhaseStateMarginal
          (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries) mu0 i) i ≤ phaseBound i) :
    CostedPhaseKernelRefinement
      (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries)
      (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries) mu0 m phaseBound := by
  let rho i := costedPhaseStateMarginal
    (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries) mu0 i
  have hrho (i : Nat) : IsProbabilityMeasure (rho i) := by
    dsimp only [rho, costedPhaseStateMarginal, costedPhaseOneRunLaw]
    letI : IsProbabilityMeasure
        (Ttc.SequentialCost.execution
          (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries) mu0) := inferInstance
    exact Measure.isProbabilityMeasure_map
      (measurable_snd.comp (measurable_pi_apply i)).aemeasurable
  apply selfRetryCostedPhaseRefinement K hK delta sigmaSq shrink hdelta hshrink
    retrySteps retries mu0 m phaseBound
  intro i hi
  letI := hrho i
  rw [lintegral_stepMean_selfRetryCostedSchedule]
  exact hquery i hi

/-- A fixed-input one-run certificate, ready for the existing outer query cutoff and
median capstone.  The accuracy premise deliberately refers to the exact self-retry state
path.  In the CV application that state must still be augmented to retain both the score
sample and the next warm seed; this theorem does not identify the state-only schedule with
that augmented algorithm. -/
theorem sourceOneRunCertificate_of_selfRetryQueryMeans
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat → ENNReal)
    (hquery : ∀ i, i < m →
      selfRetryPhaseQueryMean K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries
        (costedPhaseStateMarginal
          (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries) mu0 i) i ≤ phaseBound i)
    (est : StatePath n → Real) (hest : Measurable est)
    {runtimeConstant R eps lo hi : Real}
    (hsum : (∑ i ∈ Finset.range m, phaseBound i) ≤
      sourceOneRunQueryBudget runtimeConstant n R eps)
    (haccuracy : 4 / 5 ≤
      (inhomogeneousPathMeasure
        (selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries) mu0).real
        {omega | est omega ∈ Icc lo hi}) :
    SourceOneRunCertificate
      (costedPhaseOneRunLaw
        (selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries) mu0)
      (costedPhaseOneRunQueries m) (costedPhaseOneRunValue est)
      runtimeConstant n R eps lo hi := by
  let Q := selfRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
    retrySteps retries
  let P := selfRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
    retrySteps retries
  have hop : CostedPhaseKernelRefinement P Q mu0 m phaseBound :=
    selfRetryCostedPhaseRefinement_of_queryMeans K hK delta sigmaSq shrink
      hdelta hshrink retrySteps retries mu0 m phaseBound hquery
  letI : IsProbabilityMeasure (costedPhaseOneRunLaw Q mu0) := by
    unfold costedPhaseOneRunLaw
    infer_instance
  refine
    { probability := inferInstance
      cost_measurable := measurable_costedPhaseOneRunQueries m
      value_measurable := measurable_costedPhaseOneRunValue hest
      expected_queries := ?_
      accuracy := ?_ }
  · exact (expected_costedPhaseOneRunQueries_le_of_phaseMeans Q mu0 m phaseBound
      hop.phaseMean).trans hsum
  · have hpath : Measure.map (statePath (n := n))
        (costedPhaseOneRunLaw Q mu0) = inhomogeneousPathMeasure P mu0 := by
      change Measure.map (Ttc.SequentialCostedPathLumping.pathMap Prod.snd)
        (Ttc.SequentialCost.execution Q mu0) = _
      exact Ttc.SequentialCostedPathLumping.map_statePath_execution
        Q P mu0 hop.forgetCost
    let G : Set (StatePath n) := {omega | est omega ∈ Icc lo hi}
    have hG : MeasurableSet G := measurableSet_Icc.preimage hest
    have heq : (costedPhaseOneRunLaw Q mu0).real (statePath ⁻¹' G) =
        (inhomogeneousPathMeasure P mu0).real G :=
      measureReal_stateEvent_eq_of_path_lumping Q P mu0 hpath G hG
    change 4 / 5 ≤ (costedPhaseOneRunLaw Q mu0).real (statePath ⁻¹' G)
    rw [heq]
    exact haccuracy

#print axioms lintegral_stepMean_selfRetryCostedSchedule
#print axioms selfRetryCostedPhaseRefinement_of_queryMeans
#print axioms sourceOneRunCertificate_of_selfRetryQueryMeans

end Ttc.CVFiniteContinuingSelfCostCapstone
