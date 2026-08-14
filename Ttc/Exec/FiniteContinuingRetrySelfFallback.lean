import Ttc.Exec.FiniteContinuingRetryGeneralDecomposition
import Arlib.Probability.WarmMixture

/-! A finite retry machine whose unresolved tail returns its own incoming point. -/

namespace Ttc.FiniteContinuingRetrySelfFallback

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGeneralDecomposition
open scoped ENNReal Classical

variable {E C : Type*} [MeasurableSpace E] [MeasurableSpace C]

def selfEmbedding (x : E) : RetryState E E := (x, false, x, 0)

theorem measurable_selfEmbedding : Measurable (selfEmbedding : E → RetryState E E) := by
  unfold selfEmbedding
  fun_prop

noncomputable def selfInitialLaw (rho : Measure E) : Measure (RetryState E E) :=
  Measure.map selfEmbedding rho

instance selfInitialLaw.isProbabilityMeasure (rho : Measure E) [IsProbabilityMeasure rho] :
    IsProbabilityMeasure (selfInitialLaw rho) :=
  Measure.isProbabilityMeasure_map measurable_selfEmbedding.aemeasurable

noncomputable def selfMarginal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) (j : Nat) : Measure (RetryState E E) :=
  Arlib.adaptiveMarginal
    (schedule candidate A hA next hnext out hout roundCost hcost) (selfInitialLaw rho) j

instance selfMarginal.isProbabilityMeasure
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (j : Nat) :
    IsProbabilityMeasure
      (selfMarginal candidate A hA next out hnext hout roundCost hcost rho j) := by
  unfold selfMarginal
  infer_instance

/-- The unresolved part of a retry-state law, mapped through its stored output. -/
noncomputable def runningOutput (mu : Measure (RetryState E E)) : Measure E :=
  Measure.map output (mu.restrict Ttc.FiniteContinuingRetry.runningStates)

/-- Initially every state is running and its stored output is exactly the incoming point. -/
theorem runningOutput_selfInitialLaw (rho : Measure E) :
    runningOutput (selfInitialLaw rho) = rho := by
  ext T hT
  rw [runningOutput, Measure.map_apply measurable_output hT,
    Measure.restrict_apply (hT.preimage measurable_output),
    selfInitialLaw, Measure.map_apply measurable_selfEmbedding
      ((hT.preimage measurable_output).inter
        Ttc.FiniteContinuingRetry.measurableSet_runningStates)]
  have hpre : selfEmbedding ⁻¹'
      (output ⁻¹' T ∩ Ttc.FiniteContinuingRetry.runningStates) = T := by
    ext x
    simp [selfEmbedding, Ttc.FiniteContinuingRetry.runningStates, acceptedStates,
      accepted, output]
  rw [hpre]

/-- One retry can only remove mass from the unresolved stored-output sublaw. -/
theorem runningOutput_bind_retryStep_le
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (mu : Measure (RetryState E E)) (j : Nat) :
    runningOutput
      (mu.bind (schedule candidate A hA next hnext out hout roundCost hcost j)) ≤
      runningOutput mu := by
  rw [Measure.le_iff]
  intro T hT
  rw [runningOutput, Measure.map_apply measurable_output hT,
    Measure.restrict_apply (hT.preimage measurable_output),
    Measure.bind_apply
      ((hT.preimage measurable_output).inter
        Ttc.FiniteContinuingRetry.measurableSet_runningStates)
      (schedule candidate A hA next hnext out hout roundCost hcost j).aemeasurable,
    runningOutput, Measure.map_apply measurable_output hT,
    Measure.restrict_apply (hT.preimage measurable_output)]
  let S : Set (RetryState E E) := output ⁻¹' T ∩ Ttc.FiniteContinuingRetry.runningStates
  have hS : MeasurableSet S :=
    (hT.preimage measurable_output).inter
      Ttc.FiniteContinuingRetry.measurableSet_runningStates
  calc
    (∫⁻ z, schedule candidate A hA next hnext out hout roundCost hcost j z S ∂mu) ≤
        ∫⁻ z in S, (1 : ENNReal) ∂mu := by
      rw [← lintegral_indicator hS]
      apply lintegral_mono
      intro z
      change retryStep candidate A hA next hnext out hout roundCost hcost j z S ≤ _
      rw [retryStep_apply]
      by_cases hz : accepted z = true
      · rw [if_pos hz, Measure.dirac_apply' _ hS]
        simp [S, hz, Ttc.FiniteContinuingRetry.runningStates, acceptedStates]
      · rw [if_neg hz]
        have hadv : Measurable (advance A next out roundCost z) :=
          (measurable_advance hA hnext hout hcost).comp
            (measurable_const.prodMk measurable_id)
        rw [Measure.map_apply hadv hS]
        by_cases houtz : output z ∈ T
        · have hzS : z ∈ S := by
            simp [S, hz, Ttc.FiniteContinuingRetry.runningStates, acceptedStates, houtz]
          rw [Set.indicator_of_mem hzS]
          exact prob_le_one
        · have hempty : (advance A next out roundCost z) ⁻¹' S = ∅ := by
            have hzout : z.2.2.1 ∉ T := by simpa only [output] using houtz
            ext c
            by_cases hc : c ∈ A <;>
              simp [S, advance, hc, Ttc.FiniteContinuingRetry.runningStates,
                acceptedStates, accepted, output, hzout]
          rw [hempty, measure_empty]
          simp
    _ = mu S := by simp

/-- At every finite retry count the unresolved self-fallback tail is a submeasure of the
incoming law. -/
theorem runningOutput_selfMarginal_le
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (L : Nat) :
    runningOutput
      (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L) ≤ rho := by
  induction L with
  | zero =>
      simpa only [selfMarginal, Arlib.adaptiveMarginal] using
        le_of_eq (runningOutput_selfInitialLaw rho)
  | succ L ih =>
      rw [selfMarginal, Arlib.adaptiveMarginal]
      exact (runningOutput_bind_retryStep_le candidate A hA next out hnext hout roundCost
        hcost _ L).trans ih

/-- Consequently the unresolved self-fallback tail inherits every warm bound of the
incoming phase law. -/
theorem isWarm_runningOutput_selfMarginal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho pi : Measure E) [IsProbabilityMeasure rho] {M : ENNReal}
    (hwarm : IsWarm M rho pi) (L : Nat) :
    IsWarm M
      (runningOutput
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L)) pi :=
  IsWarm.of_le
    (runningOutput_selfMarginal_le candidate A hA next out hnext hout roundCost hcost rho L)
    hwarm

#print axioms runningOutput_selfInitialLaw
#print axioms runningOutput_bind_retryStep_le
#print axioms runningOutput_selfMarginal_le
#print axioms isWarm_runningOutput_selfMarginal

end Ttc.FiniteContinuingRetrySelfFallback
