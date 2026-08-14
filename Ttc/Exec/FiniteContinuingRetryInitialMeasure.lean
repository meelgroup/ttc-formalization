import Ttc.Exec.FiniteContinuingRetryGeneralDecomposition

/-! First-hit decomposition for a retry phase started from an arbitrary incoming law. -/

namespace Ttc.FiniteContinuingRetryInitialMeasure

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryDecomposition
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical BigOperators

variable {E C F : Type*} [MeasurableSpace E] [MeasurableSpace C] [MeasurableSpace F]

def initialEmbedding (fallback : F) (x : E) : RetryState E F :=
  (x, false, fallback, 0)

theorem measurable_initialEmbedding (fallback : F) :
    Measurable (initialEmbedding (E := E) fallback : E → RetryState E F) := by
  unfold initialEmbedding
  fun_prop

noncomputable def initialLawOf (rho : Measure E) (fallback : F) : Measure (RetryState E F) :=
  Measure.map (initialEmbedding fallback) rho

instance initialLawOf.isProbabilityMeasure (rho : Measure E) [IsProbabilityMeasure rho]
    (fallback : F) : IsProbabilityMeasure (initialLawOf rho fallback) :=
  Measure.isProbabilityMeasure_map (measurable_initialEmbedding fallback).aemeasurable

noncomputable def marginalOf
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) (fallback : F) (j : Nat) : Measure (RetryState E F) :=
  Arlib.adaptiveMarginal
    (Ttc.FiniteContinuingRetryGeneralDecomposition.schedule candidate A hA next hnext
      out hout roundCost hcost) (initialLawOf rho fallback) j

instance marginalOf.isProbabilityMeasure
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (fallback : F) (j : Nat) :
    IsProbabilityMeasure
      (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j) := by
  unfold marginalOf
  infer_instance

noncomputable def survivalOf
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) (fallback : F) (j : Nat) : ENNReal :=
  marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j
    Ttc.FiniteContinuingRetry.runningStates

noncomputable def proposalOf
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) (fallback : F) (j : Nat) : Measure C :=
  sampleFromKernel (candidate j)
    ((condOn
      (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j)
      Ttc.FiniteContinuingRetry.runningStates).map current)

theorem survival_mul_proposalOf_apply
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (fallback : F) (j : Nat)
    (hs0 : survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j ≠ 0)
    {B : Set C} (hB : MeasurableSet B) :
    survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j *
        proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback j B =
      ∫⁻ z in Ttc.FiniteContinuingRetry.runningStates, candidate j (current z) B
        ∂(marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j) := by
  let mu := marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j
  let sv := survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j
  let I := ∫⁻ z in Ttc.FiniteContinuingRetry.runningStates,
    candidate j (current z) B ∂mu
  have htop : sv ≠ ⊤ := measure_ne_top mu Ttc.FiniteContinuingRetry.runningStates
  have hp : proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback j B =
      sv⁻¹ * I := by
    unfold proposalOf sampleFromKernel
    rw [Measure.bind_apply hB (candidate j).aemeasurable,
      lintegral_map ((candidate j).measurable_coe hB) measurable_current,
      condOn_def, lintegral_smul_measure]
    rfl
  rw [hp]
  exact ENNReal.mul_inv_cancel_left hs0 htop

theorem survivalOf_succ
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (fallback : F) (j : Nat)
    (hs0 : survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j ≠ 0) :
    survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback (j + 1) =
      survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j *
        proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback j Aᶜ := by
  unfold survivalOf marginalOf
  rw [Arlib.adaptiveMarginal]
  let P := Ttc.FiniteContinuingRetryGeneralDecomposition.schedule candidate A hA next hnext
    out hout roundCost hcost
  rw [Measure.bind_apply Ttc.FiniteContinuingRetry.measurableSet_runningStates
    (P j).aemeasurable]
  have hfun : (fun z : RetryState E F ↦ P j z Ttc.FiniteContinuingRetry.runningStates) =
      Ttc.FiniteContinuingRetry.runningStates.indicator
        (fun z ↦ candidate j (current z) Aᶜ) := by
    funext z
    dsimp only [P]
    rw [Ttc.FiniteContinuingRetryGeneralDecomposition.schedule, retryStep_runningStates]
    by_cases hz : accepted z = true <;>
      simp [hz, Ttc.FiniteContinuingRetry.runningStates, acceptedStates]
  rw [hfun, lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
  simpa only [survivalOf, marginalOf] using
    (survival_mul_proposalOf_apply candidate A hA next hnext out hout roundCost hcost
      rho fallback j hs0 hA.compl).symm

theorem initialLawOf_acceptedOutputEvent (rho : Measure E) (fallback : F)
    {T : Set F} (hT : MeasurableSet T) :
    initialLawOf rho fallback (acceptedOutputEvent T) = 0 := by
  rw [initialLawOf, Measure.map_apply (measurable_initialEmbedding (E := E) fallback)
    (measurableSet_acceptedOutputEvent hT)]
  have hempty : initialEmbedding fallback ⁻¹' acceptedOutputEvent T = (∅ : Set E) := by
    ext x
    simp [initialEmbedding, acceptedOutputEvent, accepted]
  rw [hempty, measure_empty]

theorem acceptedOutputEvent_eq_sum_of
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (fallback : F) (L : Nat)
    (hs0 : ∀ j, j < L →
      survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j ≠ 0)
    (ha0 : ∀ j, j < L →
      proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback j A ≠ 0)
    {T : Set F} (hT : MeasurableSet T) :
    marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback L
        (acceptedOutputEvent T) =
      ∑ j ∈ Finset.range L,
        (survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j *
          proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback j A) *
        (Measure.map out (condOn
          (proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback j) A)) T := by
  let P := Ttc.FiniteContinuingRetryGeneralDecomposition.schedule candidate A hA next hnext
    out hout roundCost hcost
  let mu0 := initialLawOf rho fallback
  let g : Nat → RetryState E F → ENNReal := fun j z ↦
    candidate j (current z) (A ∩ out ⁻¹' T)
  have hg : ∀ j, Measurable (g j) := fun j ↦
    ((candidate j).measurable_coe (hA.inter (hT.preimage hout))).comp measurable_current
  have hstep : ∀ j z, P j z (acceptedOutputEvent T) =
      if z ∈ (acceptedStates : Set (RetryState E F)) then
        (acceptedOutputEvent T).indicator (fun _ ↦ (1 : ENNReal)) z else g j z := by
    intro j z
    have hh := retryStep_acceptedOutputEvent candidate A hA next hnext out hout roundCost
      hcost j z hT
    dsimp only [P]
    rw [Ttc.FiniteContinuingRetryGeneralDecomposition.schedule, hh]
    by_cases hz : accepted z = true
    · simp only [hz, if_pos]
      by_cases ht : z ∈ acceptedOutputEvent T <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht, acceptedStates, hz]
    · simp [hz, acceptedStates, g]
  have htel := Ttc.FiniteContinuingRetryDecomposition.adaptiveMarginal_absorbingEvent_eq_sum
    P mu0 measurableSet_acceptedStates (measurableSet_acceptedOutputEvent hT)
    (fun _ hz ↦ hz.1) g hg hstep L
  rw [initialLawOf_acceptedOutputEvent rho fallback hT, zero_add] at htel
  change Arlib.adaptiveMarginal P mu0 L (acceptedOutputEvent T) = _
  rw [htel]
  apply Finset.sum_congr rfl
  intro j hj
  let p := proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback j
  have hpTop : p A ≠ ⊤ := by
    haveI : IsProbabilityMeasure p := by
      unfold p proposalOf sampleFromKernel
      letI : IsProbabilityMeasure (condOn
          (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j)
          Ttc.FiniteContinuingRetry.runningStates) := Arlib.isProbabilityMeasure_condOn _
        (hs0 j (Finset.mem_range.1 hj)) (measure_ne_top _ _)
      letI : IsProbabilityMeasure ((condOn
          (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j)
          Ttc.FiniteContinuingRetry.runningStates).map current) :=
        Measure.isProbabilityMeasure_map measurable_current.aemeasurable
      infer_instance
    exact measure_ne_top p A
  rw [Measure.map_apply hout hT, condOn_apply p hA (hT.preimage hout)]
  change (∫⁻ z in Ttc.FiniteContinuingRetry.runningStates,
      candidate j (current z) (A ∩ out ⁻¹' T)
      ∂(marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j)) = _
  rw [← survival_mul_proposalOf_apply candidate A hA next hnext out hout roundCost hcost
    rho fallback j (hs0 j (Finset.mem_range.1 hj)) (hA.inter (hT.preimage hout))]
  change _ = (_ * p A) * (p (out ⁻¹' T ∩ A) / p A)
  rw [show out ⁻¹' T ∩ A = A ∩ out ⁻¹' T from inter_comm _ _, div_eq_mul_inv]
  have hcanc : p A * (p A)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ha0 j (Finset.mem_range.1 hj)) hpTop
  calc
    _ = (p A * (p A)⁻¹) *
        (survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j *
          p (A ∩ out ⁻¹' T)) := by rw [hcanc, one_mul]
    _ = _ := by ac_rfl

/-- Distributional-initial-law counterpart of the finite accepted-mixture TV capstone. -/
theorem tvLe_cutoffOutput_of_accepted_initialLaw
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (rho : Measure E) [IsProbabilityMeasure rho] (fallback : F) (L : Nat)
    (target : Measure F) [IsProbabilityMeasure target]
    (eta r acceptedError : ENNReal)
    (hs0 : ∀ j, survivalOf candidate A hA next hnext out hout roundCost hcost
      rho fallback j ≠ 0)
    (ha0 : ∀ j, proposalOf candidate A hA next hnext out hout roundCost hcost
      rho fallback j A ≠ 0)
    (haccepted : ∀ i : Fin L, TVLe
      (Measure.map out (condOn
        (proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback i) A))
      target acceptedError)
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤ survivalOf candidate A hA next hnext out hout roundCost hcost
      rho fallback j → proposalOf candidate A hA next hnext out hout roundCost hcost
        rho fallback j Aᶜ ≤ r) :
    TVLe
      (Measure.map (cutoffOutput (E := E) fallback)
        (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback L))
      target (acceptedError + (eta + r ^ L)) := by
  let p : Nat → Measure C := fun j ↦
    proposalOf candidate A hA next hnext out hout roundCost hcost rho fallback j
  have hpall : ∀ j, IsProbabilityMeasure (p j) := by
    intro j
    dsimp only [p]
    unfold proposalOf sampleFromKernel
    letI : IsProbabilityMeasure (condOn
        (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j)
        Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ (hs0 j) (measure_ne_top _ _)
    letI : IsProbabilityMeasure ((condOn
        (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback j)
        Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    infer_instance
  letI : ∀ j, IsProbabilityMeasure (p j) := hpall
  let w : Fin L → ENNReal := fun i ↦
    survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback i * p i A
  let q : Fin L → Measure F := fun i ↦ Measure.map out (condOn (p i) A)
  let sN : Nat → ENNReal := fun j ↦
    survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j
  have hqprob : ∀ i, IsProbabilityMeasure (q i) := by
    intro i
    dsimp only [q]
    letI : IsProbabilityMeasure (condOn (p i) A) :=
      Arlib.isProbabilityMeasure_condOn _ (by simpa only [p] using ha0 i) (measure_ne_top _ _)
    exact Measure.isProbabilityMeasure_map hout.aemeasurable
  letI : ∀ i, IsProbabilityMeasure (q i) := hqprob
  have houtEq : Measure.map (cutoffOutput (E := E) fallback)
      (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback L) =
      Ttc.ContinuingRejectionSignificant.acceptedMixture L w q (sN L) fallback := by
    have hgeneric := map_cutoffOutput_eq_acceptedMixture_of_apply
      (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback L)
      L w q fallback (by
        intro T hT
        have hacc := acceptedOutputEvent_eq_sum_of candidate A hA next hnext out hout
          roundCost hcost rho fallback L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j) hT
        rw [← Fin.sum_univ_eq_sum_range] at hacc
        simpa only [w, q, p, sN] using hacc)
    simpa only [sN, survivalOf,
      Ttc.FiniteContinuingRetryDecomposition.runningStates,
      Ttc.FiniteContinuingRetry.runningStates] using hgeneric
  have hmass : (∑ i, w i) + sN L = 1 := by
    have hpart := accepted_add_survival_eq_one
      (marginalOf candidate A hA next hnext out hout roundCost hcost rho fallback L)
    have hacc := acceptedOutputEvent_eq_sum_of candidate A hA next hnext out hout roundCost
      hcost rho fallback L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j)
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set F))
    rw [hacc, ← Fin.sum_univ_eq_sum_range] at hpart
    simpa only [w, q, p, sN, survivalOf,
      Ttc.FiniteContinuingRetryDecomposition.runningStates,
      Ttc.FiniteContinuingRetry.runningStates, measure_univ, mul_one] using hpart
  have hsbase : sN 0 ≤ 1 := prob_le_one
  have hsmono : ∀ j, sN (j + 1) ≤ sN j := by
    intro j
    dsimp only [sN]
    rw [survivalOf_succ candidate A hA next hnext out hout roundCost hcost rho fallback j
      (hs0 j)]
    exact (mul_le_mul_left' prob_le_one _).trans_eq (mul_one _)
  have hscontract : ∀ j, eta ≤ sN j → sN (j + 1) ≤ r * sN j := by
    intro j hj
    dsimp only [sN] at hj ⊢
    rw [survivalOf_succ candidate A hA next hnext out hout roundCost hcost rho fallback j
      (hs0 j)]
    simpa only [p, mul_comm] using
      (mul_le_mul_left' (hreject j hj)
        (survivalOf candidate A hA next hnext out hout roundCost hcost rho fallback j))
  have htail := Ttc.ContinuingRejectionSignificant.survival_le_eta_add_pow
    sN hsbase hr hsmono hscontract L
  rw [houtEq]
  have hbase := Ttc.ContinuingRejectionSignificant.tvLe_acceptedMixture
    L w q target (sN L) acceptedError fallback hmass (by
      intro i
      simpa only [q, p] using haccepted i)
  exact hbase.mono (by gcongr)

#print axioms survival_mul_proposalOf_apply
#print axioms survivalOf_succ
#print axioms acceptedOutputEvent_eq_sum_of
#print axioms tvLe_cutoffOutput_of_accepted_initialLaw

end Ttc.FiniteContinuingRetryInitialMeasure
