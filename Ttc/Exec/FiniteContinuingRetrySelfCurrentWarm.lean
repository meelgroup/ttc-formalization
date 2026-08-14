import Ttc.Exec.FiniteContinuingRetrySelfDecomposition

/-! Unnormalised surviving-current warmness for self-fallback retry machines. -/

namespace Ttc.FiniteContinuingRetrySelfCurrentWarm

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGeneralDecomposition
open Ttc.FiniteContinuingRetrySelfFallback
open Ttc.FiniteContinuingRetrySelfDecomposition
open scoped ENNReal Classical BigOperators

variable {E C : Type*} [MeasurableSpace E] [MeasurableSpace C]

/-- The unnormalised law of the current point on executions which have not accepted. -/
noncomputable def runningCurrent (mu : Measure (RetryState E E)) : Measure E :=
  Measure.map current (mu.restrict Ttc.FiniteContinuingRetry.runningStates)

/-- The killed transition used by a rejected retry. -/
noncomputable def rejectedKernel
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A) (next : C → E) (hnext : Measurable next)
    (j : Nat) : Kernel E E :=
  Kernel.map ((candidate j).restrict hA.compl) next

/-- The killed transition used by an accepted retry. -/
noncomputable def acceptedKernel
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A) (out : C → E) (hout : Measurable out)
    (j : Nat) : Kernel E E :=
  Kernel.map ((candidate j).restrict hA) out

theorem runningCurrent_selfInitialLaw (rho : Measure E) :
    runningCurrent (selfInitialLaw rho) = rho := by
  ext T hT
  rw [runningCurrent, Measure.map_apply measurable_current hT,
    Measure.restrict_apply (hT.preimage measurable_current), selfInitialLaw,
    Measure.map_apply measurable_selfEmbedding
      ((hT.preimage measurable_current).inter
        Ttc.FiniteContinuingRetry.measurableSet_runningStates)]
  have hpre : selfEmbedding ⁻¹'
      (current ⁻¹' T ∩ Ttc.FiniteContinuingRetry.runningStates) = T := by
    ext x
    simp [selfEmbedding, Ttc.FiniteContinuingRetry.runningStates, acceptedStates,
      accepted, current]
  rw [hpre]

/-- Exact unnormalised recurrence: surviving currents are advanced by the candidate
restricted to rejection. -/
theorem runningCurrent_selfMarginal_succ
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (j : Nat) :
    runningCurrent
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho (j + 1)) =
      (runningCurrent
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho j)).bind
          (rejectedKernel candidate A hA next hnext j) := by
  ext T hT
  let mu := selfMarginal candidate A hA next out hnext hout roundCost hcost rho j
  rw [runningCurrent, Measure.map_apply measurable_current hT,
    Measure.restrict_apply (hT.preimage measurable_current)]
  change Arlib.adaptiveMarginal
      (schedule candidate A hA next hnext out hout roundCost hcost)
      (selfInitialLaw rho) (j + 1)
      (current ⁻¹' T ∩ Ttc.FiniteContinuingRetry.runningStates) = _
  rw [Arlib.adaptiveMarginal, Measure.bind_apply
    ((hT.preimage measurable_current).inter
      Ttc.FiniteContinuingRetry.measurableSet_runningStates)
    (schedule candidate A hA next hnext out hout roundCost hcost j).aemeasurable]
  rw [Measure.bind_apply hT (rejectedKernel candidate A hA next hnext j).aemeasurable,
    runningCurrent,
    lintegral_map ((rejectedKernel candidate A hA next hnext j).measurable_coe hT)
      measurable_current,
    ← lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
  apply lintegral_congr
  intro z
  by_cases hz : accepted z = true
  · have hzrun : z ∉ (Ttc.FiniteContinuingRetry.runningStates : Set (RetryState E E)) := by
      simpa [Ttc.FiniteContinuingRetry.runningStates, acceptedStates] using hz
    rw [Set.indicator_of_notMem hzrun]
    rw [schedule, retryStep_apply, if_pos hz,
      Measure.dirac_apply' _
        ((hT.preimage measurable_current).inter
          Ttc.FiniteContinuingRetry.measurableSet_runningStates)]
    simp [hz, Ttc.FiniteContinuingRetry.runningStates, acceptedStates]
  · have hzrun : z ∈ (Ttc.FiniteContinuingRetry.runningStates : Set (RetryState E E)) := by
      simpa [Ttc.FiniteContinuingRetry.runningStates, acceptedStates] using hz
    rw [Set.indicator_of_mem hzrun]
    rw [schedule, retryStep_apply, if_neg hz]
    have hadv : Measurable (advance A next out roundCost z) :=
      (measurable_advance hA hnext hout hcost).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hadv
      ((hT.preimage measurable_current).inter
        Ttc.FiniteContinuingRetry.measurableSet_runningStates)]
    rw [rejectedKernel, Kernel.map_apply _ hnext,
      Measure.map_apply hnext hT,
      Kernel.restrict_apply' (candidate j) hA.compl _ (hT.preimage hnext)]
    congr 1
    ext c
    by_cases hc : c ∈ A <;>
      simp [advance, hc, Ttc.FiniteContinuingRetry.runningStates, acceptedStates,
        accepted, current]

/-- If each ideal killed rejection transition is a submeasure of `pi`, every
unnormalised surviving-current law retains the incoming warmness constant. -/
theorem isWarm_runningCurrent_selfMarginal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho pi : Measure E) [IsProbabilityMeasure rho] {M : ENNReal}
    (hrho : IsWarm M rho pi)
    (hreject : ∀ j, pi.bind (rejectedKernel candidate A hA next hnext j) ≤ pi) :
    ∀ j, IsWarm M
      (runningCurrent
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho j)) pi := by
  intro j
  induction j with
  | zero => simpa [selfMarginal, Arlib.adaptiveMarginal, runningCurrent_selfInitialLaw] using hrho
  | succ j ih =>
      rw [runningCurrent_selfMarginal_succ candidate A hA next out hnext hout
        roundCost hcost rho j]
      have hstep := ih.bind (rejectedKernel candidate A hA next hnext j)
      exact hstep.trans (IsWarm.of_le (hreject j) (IsWarm.refl pi)) |>.mono (by simp)

/-- The accepted first-hit increment inherits the surviving-current warmness.  Its only
target-specific input is domination of the ideal accepted killed transition. -/
theorem isWarm_firstHitIncrement
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho pi target : Measure E) [IsProbabilityMeasure rho] {M Cwarm : ENNReal}
    (hrunning : ∀ j, IsWarm M
      (runningCurrent
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho j)) pi)
    (haccept : ∀ j, IsWarm Cwarm (pi.bind (acceptedKernel candidate A hA out hout j)) target)
    (j : Nat) :
    IsWarm (Cwarm * M)
      (firstHitIncrement candidate A hA next out hnext hout roundCost hcost rho j) target := by
  have hstep := (hrunning j).bind (acceptedKernel candidate A hA out hout j)
  have htrans := hstep.trans (haccept j)
  have heq :
      (runningCurrent
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho j)).bind
          (acceptedKernel candidate A hA out hout j) =
        firstHitIncrement candidate A hA next out hnext hout roundCost hcost rho j := by
    ext T hT
    rw [Measure.bind_apply hT (acceptedKernel candidate A hA out hout j).aemeasurable]
    simp_rw [acceptedKernel, Kernel.map_apply _ hout, Measure.map_apply hout hT]
    rw [firstHitIncrement, Measure.map_apply hout hT]
    unfold sampleFromKernel
    rw [Measure.bind_apply (hT.preimage hout) ((candidate j).restrict hA).aemeasurable]
    rfl
  rw [heq] at htrans
  simpa [mul_comm] using htrans

/-- End-to-end self-fallback warmness from killed-transition domination.  This exposes
precisely the two cross-phase relations a concrete Gaussian schedule must discharge:
rejected endpoints return below the current speedy target, while accepted outputs must be
warm for the next phase's speedy target. -/
theorem isWarm_map_output_selfMarginal_of_killedTransitions
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho pi target : Measure E) [IsProbabilityMeasure rho] (L : Nat)
    {M Cwarm : ENNReal} (hrho : IsWarm M rho pi)
    (hrhoTarget : IsWarm M rho target)
    (hreject : ∀ j, pi.bind (rejectedKernel candidate A hA next hnext j) ≤ pi)
    (haccept : ∀ j,
      IsWarm Cwarm (pi.bind (acceptedKernel candidate A hA out hout j)) target) :
    IsWarm ((L : ENNReal) * (Cwarm * M) + M)
      (Measure.map output
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L)) target := by
  have hrunning := isWarm_runningCurrent_selfMarginal candidate A hA next out hnext hout
    roundCost hcost rho pi hrho hreject
  apply isWarm_map_output_selfMarginal_of_firstHit candidate A hA next out hnext hout
    roundCost hcost rho target L hrhoTarget
  intro i
  exact isWarm_firstHitIncrement candidate A hA next out hnext hout roundCost hcost
    rho pi target hrunning haccept i

end Ttc.FiniteContinuingRetrySelfCurrentWarm

#print axioms Ttc.FiniteContinuingRetrySelfCurrentWarm.runningCurrent_selfMarginal_succ
#print axioms Ttc.FiniteContinuingRetrySelfCurrentWarm.isWarm_runningCurrent_selfMarginal
#print axioms Ttc.FiniteContinuingRetrySelfCurrentWarm.isWarm_firstHitIncrement
#print axioms Ttc.FiniteContinuingRetrySelfCurrentWarm.isWarm_map_output_selfMarginal_of_killedTransitions
