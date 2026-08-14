import Ttc.Exec.FiniteContinuingRetrySelfFallback
import Ttc.Volume.CVFiniteRetryWarmFallback

/-!
# Exact first-hit decomposition for a self-fallback retry law

The unresolved output stored by the retry state is its own incoming point.  This file
decomposes the final output law into unnormalised first-hit increments and that unresolved
self tail, then packages the resulting warmness theorem.
-/

namespace Ttc.FiniteContinuingRetrySelfDecomposition

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGeneralDecomposition
open Ttc.FiniteContinuingRetrySelfFallback
open scoped ENNReal Classical BigOperators

variable {E C : Type*} [MeasurableSpace E] [MeasurableSpace C]

/-- The unnormalised output law contributed by the first acceptance at retry `j`.
The source measure is restricted to states still running at `j`; the candidate kernel is
restricted to the acceptance event before mapping through the accepted-output map. -/
noncomputable def firstHitIncrement
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) (j : Nat) : Measure E :=
  Measure.map out
    (sampleFromKernel ((candidate j).restrict hA)
      (Measure.map current
        ((selfMarginal candidate A hA next out hnext hout roundCost hcost rho j).restrict
          Ttc.FiniteContinuingRetry.runningStates)))

theorem firstHitIncrement_apply
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) (j : Nat) {T : Set E} (hT : MeasurableSet T) :
    firstHitIncrement candidate A hA next out hnext hout roundCost hcost rho j T =
      ∫⁻ z in Ttc.FiniteContinuingRetry.runningStates,
        candidate j (current z) (A ∩ out ⁻¹' T)
        ∂(selfMarginal candidate A hA next out hnext hout roundCost hcost rho j) := by
  rw [firstHitIncrement, Measure.map_apply hout hT]
  unfold sampleFromKernel
  rw [Measure.bind_apply (hT.preimage hout) ((candidate j).restrict hA).aemeasurable]
  simp_rw [Kernel.restrict_apply' (candidate j) hA _ (hT.preimage hout)]
  rw [lintegral_map
    ((candidate j).measurable_coe ((hT.preimage hout).inter hA)) measurable_current]
  simp only [inter_comm]

/-- Accepted outputs telescope into the unnormalised first-hit integrals for the
distributional self initial law. -/
theorem acceptedOutputEvent_eq_sum_firstHit
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (L : Nat)
    {T : Set E} (hT : MeasurableSet T) :
    selfMarginal candidate A hA next out hnext hout roundCost hcost rho L
        (acceptedOutputEvent T) =
      ∑ j ∈ Finset.range L,
        ∫⁻ z in Ttc.FiniteContinuingRetry.runningStates,
          candidate j (current z) (A ∩ out ⁻¹' T)
          ∂(selfMarginal candidate A hA next out hnext hout roundCost hcost rho j) := by
  let P := schedule candidate A hA next hnext out hout roundCost hcost
  let mu0 := selfInitialLaw rho
  let g : Nat → RetryState E E → ENNReal := fun j z ↦
    candidate j (current z) (A ∩ out ⁻¹' T)
  have hg : ∀ j, Measurable (g j) := fun j ↦
    ((candidate j).measurable_coe (hA.inter (hT.preimage hout))).comp measurable_current
  have hstep : ∀ j z, P j z (acceptedOutputEvent T) =
      if z ∈ (acceptedStates : Set (RetryState E E)) then
        (acceptedOutputEvent T).indicator (fun _ ↦ (1 : ENNReal)) z else g j z := by
    intro j z
    dsimp only [P]
    rw [schedule, retryStep_acceptedOutputEvent candidate A hA next hnext out hout
      roundCost hcost j z hT]
    by_cases hz : accepted z = true
    · simp only [hz, if_pos]
      by_cases ht : z ∈ acceptedOutputEvent T <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht, acceptedStates, hz]
    · simp [hz, acceptedStates, g]
  have htel :=
    Ttc.FiniteContinuingRetryDecomposition.adaptiveMarginal_absorbingEvent_eq_sum
      P mu0 measurableSet_acceptedStates (measurableSet_acceptedOutputEvent hT)
      (fun _ hz ↦ hz.1) g hg hstep L
  have hinit : mu0 (acceptedOutputEvent T) = 0 := by
    dsimp only [mu0]
    rw [selfInitialLaw, Measure.map_apply measurable_selfEmbedding
      (measurableSet_acceptedOutputEvent hT)]
    have hempty : selfEmbedding ⁻¹' acceptedOutputEvent T = (∅ : Set E) := by
      ext x
      simp [selfEmbedding, acceptedOutputEvent, accepted]
    rw [hempty, measure_empty]
  rw [hinit, zero_add] at htel
  change Arlib.adaptiveMarginal P mu0 L (acceptedOutputEvent T) = _
  simpa only [selfMarginal, P, mu0, g,
    Ttc.FiniteContinuingRetry.runningStates] using htel

/-- Exact final law: the sum of all unnormalised first-hit output increments plus the
unresolved self-fallback tail. -/
theorem map_output_selfMarginal_eq_sum_firstHit_add_tail
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (L : Nat) :
    Measure.map output
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L) =
      (∑ i : Fin L,
        firstHitIncrement candidate A hA next out hnext hout roundCost hcost rho i) +
      runningOutput
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L) := by
  ext T hT
  let mu := selfMarginal candidate A hA next out hnext hout roundCost hcost rho L
  have hunion : (output : RetryState E E → E) ⁻¹' T =
      acceptedOutputEvent (E := E) T ∪
        ((Ttc.FiniteContinuingRetry.runningStates : Set (RetryState E E)) ∩
          (output : RetryState E E → E) ⁻¹' T) := by
    ext z
    by_cases hz : accepted z = true <;>
      simp [acceptedOutputEvent, Ttc.FiniteContinuingRetry.runningStates,
        acceptedStates, hz]
  have hdisj : Disjoint (acceptedOutputEvent (E := E) T)
      ((Ttc.FiniteContinuingRetry.runningStates : Set (RetryState E E)) ∩
        (output : RetryState E E → E) ⁻¹' T) :=
    Set.disjoint_left.2 fun _ ha hr ↦ hr.1 ha.1
  rw [Measure.map_apply measurable_output hT, hunion,
    measure_union hdisj
      (Ttc.FiniteContinuingRetry.measurableSet_runningStates.inter
        (hT.preimage measurable_output)),
    Measure.add_apply,
    runningOutput, Measure.map_apply measurable_output hT,
    Measure.restrict_apply (hT.preimage measurable_output), inter_comm]
  have hsumApply :
      (∑ i : Fin L,
        firstHitIncrement candidate A hA next out hnext hout roundCost hcost rho i) T =
      ∑ i : Fin L,
        firstHitIncrement candidate A hA next out hnext hout roundCost hcost rho i T := by
    simpa only using (Measure.finsetSum_apply Finset.univ
      (fun i : Fin L ↦
        firstHitIncrement candidate A hA next out hnext hout roundCost hcost rho i) T)
  rw [hsumApply]
  have hacc := acceptedOutputEvent_eq_sum_firstHit candidate A hA next out hnext hout
    roundCost hcost rho L hT
  rw [← Fin.sum_univ_eq_sum_range] at hacc
  rw [hacc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (firstHitIncrement_apply candidate A hA next out hnext hout roundCost hcost rho i hT).symm

/-- Law-level warmness capstone.  The only analytic premise left to the concrete Gaussian
phase is a uniform warmness bound for each *unnormalised* first-hit increment. -/
theorem isWarm_map_output_selfMarginal_of_firstHit
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next out : C → E) (hnext : Measurable next) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho pi : Measure E) [IsProbabilityMeasure rho] (L : Nat)
    {M Cwarm : ENNReal} (hrho : IsWarm M rho pi)
    (hincrement : ∀ i : Fin L,
      IsWarm (Cwarm * M)
        (firstHitIncrement candidate A hA next out hnext hout roundCost hcost rho i) pi) :
    IsWarm ((L : ENNReal) * (Cwarm * M) + M)
      (Measure.map output
        (selfMarginal candidate A hA next out hnext hout roundCost hcost rho L)) pi := by
  rw [map_output_selfMarginal_eq_sum_firstHit_add_tail candidate A hA next out hnext hout
    roundCost hcost rho L]
  exact Ttc.CVFiniteRetryWarmFallback.isWarm_finiteRetry_selfFallback
    (fun i ↦ firstHitIncrement candidate A hA next out hnext hout roundCost hcost rho i)
    hrho
    (runningOutput_selfMarginal_le candidate A hA next out hnext hout roundCost hcost rho L)
    hincrement

#print axioms firstHitIncrement_apply
#print axioms acceptedOutputEvent_eq_sum_firstHit
#print axioms map_output_selfMarginal_eq_sum_firstHit_add_tail
#print axioms isWarm_map_output_selfMarginal_of_firstHit

end Ttc.FiniteContinuingRetrySelfDecomposition
