/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.FiniteContinuingRetryInitialMeasure

/-! # Warmness of a finite continuing retry with self fallback

The initial state stores the incoming point itself in the output field.  Consequently an
unresolved retry tail is a sublaw of the incoming measure, rather than a fixed fallback
atom.  This is the key domination fact needed by a subsequent phase.
-/

namespace Ttc.FiniteContinuingRetrySelfWarm

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGeneralDecomposition
open scoped ENNReal Classical

variable {E C : Type*} [MeasurableSpace E] [MeasurableSpace C]

def selfInitialEmbedding (x : E) : RetryState E E := (x, false, x, 0)

theorem measurable_selfInitialEmbedding : Measurable (selfInitialEmbedding : E → RetryState E E) := by
  unfold selfInitialEmbedding
  fun_prop

noncomputable def selfInitialLaw (rho : Measure E) : Measure (RetryState E E) :=
  rho.map selfInitialEmbedding

instance selfInitialLaw.isProbabilityMeasure (rho : Measure E) [IsProbabilityMeasure rho] :
    IsProbabilityMeasure (selfInitialLaw rho) :=
  Measure.isProbabilityMeasure_map measurable_selfInitialEmbedding.aemeasurable

noncomputable def selfMarginal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → E) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) (j : Nat) : Measure (RetryState E E) :=
  Arlib.adaptiveMarginal
    (schedule candidate A hA next hnext out hout roundCost hcost) (selfInitialLaw rho) j

instance selfMarginal.isProbabilityMeasure
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → E) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (j : Nat) :
    IsProbabilityMeasure
      (selfMarginal candidate A hA next hnext out hout roundCost hcost rho j) := by
  unfold selfMarginal
  infer_instance

def runningOutputEvent (T : Set E) : Set (RetryState E E) :=
  Ttc.FiniteContinuingRetry.runningStates ∩ output ⁻¹' T

theorem measurableSet_runningOutputEvent {T : Set E} (hT : MeasurableSet T) :
    MeasurableSet (runningOutputEvent T) :=
  Ttc.FiniteContinuingRetry.measurableSet_runningStates.inter
    (hT.preimage measurable_output)

/-- A retry can only remove mass from the unresolved self-fallback sublaw. -/
theorem selfMarginal_runningOutputEvent_antitone
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → E) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho]
    {T : Set E} (hT : MeasurableSet T) (j : Nat) :
    selfMarginal candidate A hA next hnext out hout roundCost hcost rho (j + 1)
        (runningOutputEvent T) ≤
      selfMarginal candidate A hA next hnext out hout roundCost hcost rho j
        (runningOutputEvent T) := by
  let P := schedule candidate A hA next hnext out hout roundCost hcost
  let mu := selfMarginal candidate A hA next hnext out hout roundCost hcost rho j
  unfold selfMarginal
  rw [Arlib.adaptiveMarginal, Measure.bind_apply (measurableSet_runningOutputEvent hT)
    (P j).aemeasurable]
  have hpoint : ∀ s : RetryState E E,
      P j s (runningOutputEvent T) ≤
        (runningOutputEvent T).indicator (fun _ ↦ (1 : ENNReal)) s := by
    intro s
    dsimp only [P]
    rw [schedule, retryStep_apply]
    by_cases hs : accepted s = true
    · rw [if_pos hs, Measure.dirac_apply' _ (measurableSet_runningOutputEvent hT)]
      simp [runningOutputEvent, Ttc.FiniteContinuingRetry.runningStates, acceptedStates, hs]
    · rw [if_neg hs]
      have hadv : Measurable (advance A next out roundCost s) :=
        (measurable_advance (E := E) (F := E) hA hnext hout hcost).comp
          (measurable_const.prodMk measurable_id)
      rw [Measure.map_apply hadv (measurableSet_runningOutputEvent hT)]
      by_cases hTout : output s ∈ T
      · calc
          candidate j (current s) (advance A next out roundCost s ⁻¹'
              runningOutputEvent T) ≤ 1 := prob_le_one
          _ = (runningOutputEvent T).indicator (fun _ ↦ (1 : ENNReal)) s := by
            rw [Set.indicator_of_mem]
            exact ⟨by simpa [Ttc.FiniteContinuingRetry.runningStates,
              acceptedStates] using hs, hTout⟩
      · have hpre : advance A next out roundCost s ⁻¹' runningOutputEvent T = (∅ : Set C) := by
          ext c
          simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          by_cases hc : c ∈ A
          · intro hm
            exact hm.1 (by simp [Ttc.FiniteContinuingRetry.runningStates,
              acceptedStates, advance, accepted, hc])
          · intro hm
            apply hTout
            simpa [advance, output, hc] using hm.2
        rw [hpre, measure_empty]
        exact bot_le
  calc
    (∫⁻ s, P j s (runningOutputEvent T) ∂mu) ≤
        ∫⁻ s, (runningOutputEvent T).indicator (fun _ ↦ (1 : ENNReal)) s ∂mu :=
      lintegral_mono hpoint
    _ = mu (runningOutputEvent T) :=
      lintegral_indicator_one (measurableSet_runningOutputEvent hT)

/-- At every finite cutoff, the unresolved self-fallback output is dominated by the
incoming law. -/
theorem selfMarginal_runningOutputEvent_le
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → E) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho]
    {T : Set E} (hT : MeasurableSet T) : ∀ j,
    selfMarginal candidate A hA next hnext out hout roundCost hcost rho j
        (runningOutputEvent T) ≤ rho T := by
  intro j
  induction j with
  | zero =>
      unfold selfMarginal Arlib.adaptiveMarginal selfInitialLaw
      rw [Measure.map_apply measurable_selfInitialEmbedding
        (measurableSet_runningOutputEvent hT)]
      have hpre : selfInitialEmbedding ⁻¹' runningOutputEvent T = T := by
        ext x
        simp [selfInitialEmbedding, runningOutputEvent,
          Ttc.FiniteContinuingRetry.runningStates, acceptedStates, accepted, output]
      rw [hpre]
  | succ j ih =>
      exact (selfMarginal_runningOutputEvent_antitone candidate A hA next hnext out hout
        roundCost hcost rho hT j).trans ih

/-- Raw first-hit expansion for the accepted sublaw, without normalizing any survival
event. -/
theorem selfMarginal_acceptedOutputEvent_eq_sum
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → E) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (L : Nat)
    {T : Set E} (hT : MeasurableSet T) :
    selfMarginal candidate A hA next hnext out hout roundCost hcost rho L
        (acceptedOutputEvent T) =
      ∑ j ∈ Finset.range L,
        ∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
          candidate j (current s) (A ∩ out ⁻¹' T)
          ∂(selfMarginal candidate A hA next hnext out hout roundCost hcost rho j) := by
  let P := schedule candidate A hA next hnext out hout roundCost hcost
  let mu0 := selfInitialLaw rho
  let g : Nat → RetryState E E → ENNReal := fun j s ↦
    candidate j (current s) (A ∩ out ⁻¹' T)
  have hg : ∀ j, Measurable (g j) := fun j ↦
    ((candidate j).measurable_coe (hA.inter (hT.preimage hout))).comp measurable_current
  have hstep : ∀ j s, P j s (acceptedOutputEvent T) =
      if s ∈ (acceptedStates : Set (RetryState E E)) then
        (acceptedOutputEvent T).indicator (fun _ ↦ (1 : ENNReal)) s else g j s := by
    intro j s
    dsimp only [P]
    rw [schedule, retryStep_acceptedOutputEvent candidate A hA next hnext out hout
      roundCost hcost j s hT]
    by_cases hs : accepted s = true
    · simp only [hs, if_pos]
      by_cases ht : s ∈ acceptedOutputEvent T <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht, acceptedStates, hs]
    · simp [hs, acceptedStates, g]
  have htel := Ttc.FiniteContinuingRetryDecomposition.adaptiveMarginal_absorbingEvent_eq_sum
    P mu0 measurableSet_acceptedStates (measurableSet_acceptedOutputEvent hT)
    (fun _ hs ↦ hs.1) g hg hstep L
  have hinit : mu0 (acceptedOutputEvent T) = 0 := by
    dsimp only [mu0, selfInitialLaw]
    rw [Measure.map_apply measurable_selfInitialEmbedding
      (measurableSet_acceptedOutputEvent hT)]
    have hpre : selfInitialEmbedding ⁻¹' acceptedOutputEvent T = (∅ : Set E) := by
      ext x
      simp [selfInitialEmbedding, acceptedOutputEvent, accepted]
    rw [hpre, measure_empty]
  rw [hinit, zero_add] at htel
  simpa only [selfMarginal, P, mu0, g,
    Ttc.FiniteContinuingRetryDecomposition.runningStates,
    Ttc.FiniteContinuingRetry.runningStates] using htel

noncomputable def acceptedOutputSubmeasure
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → E) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) (L : Nat) : Measure E :=
  (selfMarginal candidate A hA next hnext out hout roundCost hcost rho L).restrict
    acceptedStates |>.map output

/-- A local accepted-candidate domination proves warmness of the entire accepted first-hit
sublaw.  The acceptance factor is essential: it makes all first-hit weights sum to at most
one. -/
theorem isWarm_acceptedOutputSubmeasure_of_local
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → E) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (pi : Measure E) (L : Nat)
    {Macc : ENNReal}
    (hlocal : ∀ j (s : RetryState E E), accepted s = false →
      ∀ T, MeasurableSet T →
        candidate j (current s) (A ∩ out ⁻¹' T) ≤
          (Macc * pi T) * candidate j (current s) A) :
    IsWarm Macc
      (acceptedOutputSubmeasure candidate A hA next hnext out hout roundCost hcost rho L) pi := by
  intro T hT
  let mu : Nat → Measure (RetryState E E) := fun j ↦
    selfMarginal candidate A hA next hnext out hout roundCost hcost rho j
  let a : Nat → ENNReal := fun j ↦
    ∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
      candidate j (current s) A ∂(mu j)
  have hterm : ∀ j,
      (∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
        candidate j (current s) (A ∩ out ⁻¹' T) ∂(mu j)) ≤
        (Macc * pi T) * a j := by
    intro j
    have hmeas : Measurable (fun s : RetryState E E ↦
        (Macc * pi T) * candidate j (current s) A) :=
      measurable_const.mul ((candidate j).measurable_coe hA |>.comp measurable_current)
    calc
      (∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
          candidate j (current s) (A ∩ out ⁻¹' T) ∂(mu j)) ≤
          ∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
            (Macc * pi T) * candidate j (current s) A ∂(mu j) := by
        apply setLIntegral_mono hmeas
        intro s hs
        have hnot : ¬ accepted s = true := by
          simpa [Ttc.FiniteContinuingRetry.runningStates, acceptedStates] using hs
        exact hlocal j s (Bool.eq_false_of_not_eq_true hnot) T hT
      _ = (Macc * pi T) * a j := by
        dsimp only [a]
        change (∫⁻ s, (Macc * pi T) * candidate j (current s) A
          ∂(mu j).restrict Ttc.FiniteContinuingRetry.runningStates) = _
        exact lintegral_const_mul (μ :=
          (mu j).restrict Ttc.FiniteContinuingRetry.runningStates) (Macc * pi T)
          (((candidate j).measurable_coe hA).comp measurable_current)
  have hsumA : (∑ j ∈ Finset.range L, a j) ≤ 1 := by
    have heq := selfMarginal_acceptedOutputEvent_eq_sum candidate A hA next hnext out hout
      roundCost hcost rho L (MeasurableSet.univ : MeasurableSet (Set.univ : Set E))
    have hset : acceptedOutputEvent (E := E) (Set.univ : Set E) =
        (acceptedStates : Set (RetryState E E)) := by
      ext s
      simp [acceptedOutputEvent, acceptedStates]
    rw [hset] at heq
    have hprob : selfMarginal candidate A hA next hnext out hout roundCost hcost rho L
        (acceptedStates : Set (RetryState E E)) ≤ 1 := prob_le_one
    rw [heq] at hprob
    simpa only [mu, a, preimage_univ, inter_univ] using hprob
  have houtEq := selfMarginal_acceptedOutputEvent_eq_sum candidate A hA next hnext out hout
    roundCost hcost rho L hT
  rw [acceptedOutputSubmeasure, Measure.map_apply measurable_output hT,
    Measure.restrict_apply (hT.preimage measurable_output)]
  change selfMarginal candidate A hA next hnext out hout roundCost hcost rho L
      (output ⁻¹' T ∩ acceptedStates) ≤ Macc * pi T
  rw [show output ⁻¹' T ∩ acceptedStates = acceptedOutputEvent T by
    ext s; simp [acceptedOutputEvent, acceptedStates, and_comm]]
  rw [houtEq]
  calc
    (∑ j ∈ Finset.range L,
      ∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
        candidate j (current s) (A ∩ out ⁻¹' T) ∂(mu j)) ≤
        ∑ j ∈ Finset.range L, (Macc * pi T) * a j := by
      exact Finset.sum_le_sum fun j _ ↦ hterm j
    _ = (Macc * pi T) * ∑ j ∈ Finset.range L, a j := by
      rw [Finset.mul_sum]
    _ ≤ (Macc * pi T) * 1 := mul_le_mul_left' hsumA _
    _ = Macc * pi T := mul_one _

/-- Self fallback preserves finite warmness: accepted mass costs `Macc`, while the entire
unresolved tail costs at most the incoming `M0`.  In particular no atom appears. -/
theorem isWarm_map_output_selfFallback
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → E) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (pi : Measure E) (L : Nat)
    {M0 Macc : ENNReal} (hwarm : IsWarm M0 rho pi)
    (haccepted : IsWarm Macc
      (acceptedOutputSubmeasure candidate A hA next hnext out hout roundCost hcost rho L) pi) :
    IsWarm (Macc + M0)
      ((selfMarginal candidate A hA next hnext out hout roundCost hcost rho L).map output) pi := by
  intro T hT
  let mu := selfMarginal candidate A hA next hnext out hout roundCost hcost rho L
  have hsplit : output ⁻¹' T =
      (acceptedStates ∩ output ⁻¹' T) ∪ runningOutputEvent T := by
    ext s
    by_cases hs : accepted s = true <;>
      simp [runningOutputEvent, Ttc.FiniteContinuingRetry.runningStates, acceptedStates, hs]
  have hdisj : Disjoint (acceptedStates ∩ output ⁻¹' T) (runningOutputEvent T) := by
    exact Set.disjoint_left.2 fun _ hs hr ↦ hr.1 hs.1
  rw [Measure.map_apply measurable_output hT, hsplit,
    measure_union hdisj (measurableSet_runningOutputEvent hT)]
  have hacc : mu (acceptedStates ∩ output ⁻¹' T) ≤ Macc * pi T := by
    have hh := haccepted T hT
    rw [acceptedOutputSubmeasure, Measure.map_apply measurable_output hT,
      Measure.restrict_apply (hT.preimage measurable_output)] at hh
    simpa [inter_comm] using hh
  have htail : mu (runningOutputEvent T) ≤ M0 * pi T :=
    (selfMarginal_runningOutputEvent_le candidate A hA next hnext out hout roundCost hcost
      rho hT L).trans (hwarm T hT)
  calc
    mu (acceptedStates ∩ output ⁻¹' T) + mu (runningOutputEvent T) ≤
        Macc * pi T + M0 * pi T := add_le_add hacc htail
    _ = (Macc + M0) * pi T := by rw [add_mul]

end Ttc.FiniteContinuingRetrySelfWarm

#print axioms Ttc.FiniteContinuingRetrySelfWarm.selfMarginal_runningOutputEvent_le
#print axioms Ttc.FiniteContinuingRetrySelfWarm.isWarm_acceptedOutputSubmeasure_of_local
#print axioms Ttc.FiniteContinuingRetrySelfWarm.isWarm_map_output_selfFallback
