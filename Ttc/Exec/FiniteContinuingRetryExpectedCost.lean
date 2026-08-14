import Ttc.Exec.FiniteContinuingRetryEmbeddedSelective
import Arlib.MarkovChains.Continuous.WastedSteps

/-! Exact expected accumulated cost for an inhomogeneous continuing-retry machine. -/

namespace Ttc.FiniteContinuingRetryExpectedCost

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGeneralDecomposition
open Ttc.FiniteContinuingRetryEmbeddedSelective
open scoped ENNReal Classical BigOperators

variable {E C F X : Type*} [MeasurableSpace E] [MeasurableSpace C]
  [MeasurableSpace F] [MeasurableSpace X]

noncomputable def candidateMean
    (candidate : Nat → Kernel E C) (roundCost : C → ENNReal)
    (j : Nat) (x : E) : ENNReal :=
  ∫⁻ c, roundCost c ∂(candidate j x)

theorem measurable_candidateMean
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (roundCost : C → ENNReal)
    (hcost : Measurable roundCost) (j : Nat) :
    Measurable (candidateMean candidate roundCost j) := by
  unfold candidateMean
  exact Measurable.lintegral_kernel_prod_right (κ := candidate j)
    (hcost.comp measurable_snd)

/-- Current-point sublaw carried by executions which are still running. -/
noncomputable def runningCurrent (mu : Measure (RetryState E F)) : Measure E :=
  Measure.map current (mu.restrict Ttc.FiniteContinuingRetry.runningStates)

/-- One retry increases expected accumulated cost by exactly the candidate mean integrated
against the unnormalised surviving-current law. -/
theorem lintegral_accumulatedCost_bind_retryStep
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (mu : Measure (RetryState E F)) [IsProbabilityMeasure mu] (j : Nat) :
    (∫⁻ z, accumulatedCost z
        ∂(mu.bind (schedule candidate A hA next hnext out hout roundCost hcost j))) =
      (∫⁻ z, accumulatedCost z ∂mu) +
        ∫⁻ x, candidateMean candidate roundCost j x ∂(runningCurrent mu) := by
  rw [Measure.lintegral_bind
    (schedule candidate A hA next hnext out hout roundCost hcost j).aemeasurable
    measurable_accumulatedCost.aemeasurable]
  have hpoint : (fun z : RetryState E F ↦
      ∫⁻ z', accumulatedCost z'
        ∂(schedule candidate A hA next hnext out hout roundCost hcost j z)) =
      (fun z ↦ accumulatedCost z +
        Ttc.FiniteContinuingRetry.runningStates.indicator
          (candidateMean candidate roundCost j ∘ current) z) := by
    funext z
    rw [schedule, retryStep_apply]
    by_cases hz : accepted z = true
    · rw [if_pos hz, lintegral_dirac' z measurable_accumulatedCost]
      have hnrun : z ∉ (Ttc.FiniteContinuingRetry.runningStates : Set (RetryState E F)) := by
        simpa [Ttc.FiniteContinuingRetry.runningStates, acceptedStates] using hz
      simp [hnrun]
    · rw [if_neg hz]
      have hadv : Measurable (advance A next out roundCost z) :=
        (measurable_advance (E := E) (F := F) hA hnext hout hcost).comp
          (measurable_const.prodMk measurable_id)
      rw [lintegral_map measurable_accumulatedCost hadv]
      have hcostAdvance : (fun c : C ↦
          accumulatedCost (advance A next out roundCost z c)) =
          fun c ↦ accumulatedCost z + roundCost c := by
        funext c
        by_cases hc : c ∈ A <;> simp [advance, hc, accumulatedCost]
      rw [hcostAdvance, lintegral_add_left]
      · rw [lintegral_const, measure_univ, mul_one]
        have hzrun : z ∈ (Ttc.FiniteContinuingRetry.runningStates : Set (RetryState E F)) := by
          simpa [Ttc.FiniteContinuingRetry.runningStates, acceptedStates] using hz
        simp [Set.indicator_of_mem hzrun, candidateMean, Function.comp_apply]
      · exact measurable_const
  rw [hpoint, lintegral_add_left]
  · rw [runningCurrent, lintegral_map
      ((measurable_candidateMean candidate roundCost hcost j)) measurable_current,
      lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
    simp only [Function.comp_apply]
  · exact measurable_accumulatedCost

/-- The finite-horizon mean is the sum of the actual per-retry means over unnormalised
surviving-current laws.  The initial embedding is assumed to record zero cost. -/
theorem lintegral_accumulatedCost_embeddedMarginal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (hzero : ∀ x, accumulatedCost (embed x) = 0)
    (rho : Measure X) [IsProbabilityMeasure rho] (L : Nat) :
    (∫⁻ z, accumulatedCost z
      ∂(embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L)) =
      ∑ j ∈ Finset.range L,
        ∫⁻ x, candidateMean candidate roundCost j x
          ∂(runningCurrent
            (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)) := by
  letI : ∀ j, IsProbabilityMeasure
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j) :=
    fun j ↦ isProbabilityMeasure_embeddedMarginal candidate A hA next hnext out hout
      roundCost hcost embed hembed rho j
  induction L with
  | zero =>
      rw [embeddedMarginal, Arlib.adaptiveMarginal]
      rw [lintegral_map measurable_accumulatedCost hembed]
      simp [hzero]
  | succ L ih =>
      change (∫⁻ z, accumulatedCost z
        ∂((embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L).bind
          (schedule candidate A hA next hnext out hout roundCost hcost L))) = _
      rw [lintegral_accumulatedCost_bind_retryStep candidate A hA next hnext out hout
        roundCost hcost]
      change (∫⁻ z, accumulatedCost z
        ∂(embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L)) +
          _ = _
      rw [ih, Finset.sum_range_succ]

/-- Warmness converts the exact retry sum into a reference-law cost bound. -/
theorem lintegral_accumulatedCost_embeddedMarginal_le
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (hzero : ∀ x, accumulatedCost (embed x) = 0)
    (rho : Measure X) [IsProbabilityMeasure rho] (L : Nat)
    (pi : Measure E) (M : ENNReal)
    (hwarm : ∀ j, j < L → IsWarm M
      (runningCurrent
        (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)) pi) :
    (∫⁻ z, accumulatedCost z
      ∂(embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L)) ≤
      ∑ j ∈ Finset.range L, M *
        ∫⁻ x, candidateMean candidate roundCost j x ∂pi := by
  rw [lintegral_accumulatedCost_embeddedMarginal candidate A hA next hnext out hout
    roundCost hcost embed hembed hzero rho L]
  apply Finset.sum_le_sum
  intro j hj
  exact Arlib.MarkovChains.lintegral_le_of_isWarm (hwarm j (Finset.mem_range.1 hj))
    (candidateMean candidate roundCost j)

#print axioms lintegral_accumulatedCost_embeddedMarginal
#print axioms lintegral_accumulatedCost_embeddedMarginal_le

end Ttc.FiniteContinuingRetryExpectedCost
