import Ttc.Exec.FiniteContinuingRetrySelfSelective
import Ttc.Exec.FiniteContinuingRetryInitialMeasure

/-!
# Selective retry decomposition for a measurable, variable-fallback embedding

Unlike `FiniteContinuingRetryInitialMeasure`, the stored cutoff output may depend on the
incoming point.  The running-chain state and the stored output may also have different
types.  This is the interface needed by the Gaussian `(score, seed)` phase.
-/

namespace Ttc.FiniteContinuingRetryEmbeddedSelective

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryDecomposition
open Ttc.FiniteContinuingRetryGeneralDecomposition
open Ttc.FiniteContinuingRetrySelfSelective
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical BigOperators

variable {X E C F : Type*} [MeasurableSpace X] [MeasurableSpace E]
  [MeasurableSpace C] [MeasurableSpace F]

noncomputable def embeddedMarginal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (rho : Measure X) (j : Nat) :
    Measure (RetryState E F) :=
  Arlib.adaptiveMarginal
    (schedule candidate A hA next hnext out hout roundCost hcost)
    (Measure.map embed rho) j

theorem isProbabilityMeasure_embeddedMarginal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (rho : Measure X) [IsProbabilityMeasure rho] (j : Nat) :
    IsProbabilityMeasure
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j) := by
  unfold embeddedMarginal
  letI : IsProbabilityMeasure (Measure.map embed rho) :=
    Measure.isProbabilityMeasure_map hembed.aemeasurable
  infer_instance

noncomputable def embeddedSurvival
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (rho : Measure X) (j : Nat) : ENNReal :=
  embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j
    Ttc.FiniteContinuingRetry.runningStates

noncomputable def embeddedProposal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (rho : Measure X) (j : Nat) : Measure C :=
  sampleFromKernel (candidate j)
    ((condOn
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)
      Ttc.FiniteContinuingRetry.runningStates).map current)

noncomputable def embeddedRunningOutput (mu : Measure (RetryState E F)) : Measure F :=
  Measure.map output (mu.restrict Ttc.FiniteContinuingRetry.runningStates)

theorem embeddedSurvival_mul_proposal_apply
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (rho : Measure X) [IsProbabilityMeasure rho] (j : Nat)
    (hs0 : embeddedSurvival candidate A hA next hnext out hout roundCost hcost
      embed rho j ≠ 0)
    {B : Set C} (hB : MeasurableSet B) :
    embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j *
        embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho j B =
      ∫⁻ z in Ttc.FiniteContinuingRetry.runningStates, candidate j (current z) B
        ∂(embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j) := by
  letI := isProbabilityMeasure_embeddedMarginal candidate A hA next hnext out hout
    roundCost hcost embed hembed rho j
  let mu := embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j
  let sv := embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j
  let I := ∫⁻ z in Ttc.FiniteContinuingRetry.runningStates,
    candidate j (current z) B ∂mu
  have htop : sv ≠ ⊤ := measure_ne_top mu Ttc.FiniteContinuingRetry.runningStates
  have hp : embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho j B =
      sv⁻¹ * I := by
    unfold embeddedProposal sampleFromKernel
    rw [Measure.bind_apply hB (candidate j).aemeasurable,
      lintegral_map ((candidate j).measurable_coe hB) measurable_current,
      condOn_def, lintegral_smul_measure]
    rfl
  rw [hp]
  exact ENNReal.mul_inv_cancel_left hs0 htop

theorem embeddedSurvival_succ
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (rho : Measure X) [IsProbabilityMeasure rho] (j : Nat)
    (hs0 : embeddedSurvival candidate A hA next hnext out hout roundCost hcost
      embed rho j ≠ 0) :
    embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho (j + 1) =
      embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j *
        embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho j Aᶜ := by
  letI := isProbabilityMeasure_embeddedMarginal candidate A hA next hnext out hout
    roundCost hcost embed hembed rho j
  unfold embeddedSurvival embeddedMarginal
  rw [Arlib.adaptiveMarginal]
  let P := schedule candidate A hA next hnext out hout roundCost hcost
  rw [Measure.bind_apply Ttc.FiniteContinuingRetry.measurableSet_runningStates
    (P j).aemeasurable]
  have hfun : (fun z : RetryState E F ↦ P j z Ttc.FiniteContinuingRetry.runningStates) =
      Ttc.FiniteContinuingRetry.runningStates.indicator
        (fun z ↦ candidate j (current z) Aᶜ) := by
    funext z
    dsimp only [P]
    rw [schedule, retryStep_runningStates]
    by_cases hz : accepted z = true <;>
      simp [hz, Ttc.FiniteContinuingRetry.runningStates, acceptedStates]
  rw [hfun, lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
  simpa only [embeddedSurvival, embeddedMarginal] using
    (embeddedSurvival_mul_proposal_apply candidate A hA next hnext out hout roundCost hcost
      embed hembed rho j hs0 hA.compl).symm

theorem embeddedInitial_acceptedOutputEvent
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (hRunning : ∀ x, accepted (embed x) ≠ true) (rho : Measure X)
    {T : Set F} (hT : MeasurableSet T) :
    Measure.map embed rho (acceptedOutputEvent T) = 0 := by
  rw [Measure.map_apply hembed (measurableSet_acceptedOutputEvent hT)]
  have hempty : embed ⁻¹' acceptedOutputEvent T = (∅ : Set X) := by
    ext x
    simp [acceptedOutputEvent, hRunning x]
  rw [hempty, measure_empty]

theorem acceptedOutputEvent_eq_sum_embedded
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (hRunning : ∀ x, accepted (embed x) ≠ true)
    (rho : Measure X) [IsProbabilityMeasure rho] (L : Nat)
    (hs0 : ∀ j, j < L → embeddedSurvival candidate A hA next hnext out hout
      roundCost hcost embed rho j ≠ 0)
    (ha0 : ∀ j, j < L → embeddedProposal candidate A hA next hnext out hout
      roundCost hcost embed rho j A ≠ 0)
    {T : Set F} (hT : MeasurableSet T) :
    embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L
        (acceptedOutputEvent T) =
      ∑ j ∈ Finset.range L,
        (embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j *
          embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho j A) *
        (Measure.map out (condOn
          (embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho j) A)) T := by
  let P := schedule candidate A hA next hnext out hout roundCost hcost
  let mu0 := Measure.map embed rho
  let g : Nat → RetryState E F → ENNReal := fun j z ↦
    candidate j (current z) (A ∩ out ⁻¹' T)
  have hg : ∀ j, Measurable (g j) := fun j ↦
    ((candidate j).measurable_coe (hA.inter (hT.preimage hout))).comp measurable_current
  have hstep : ∀ j z, P j z (acceptedOutputEvent T) =
      if z ∈ (acceptedStates : Set (RetryState E F)) then
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
  letI : IsProbabilityMeasure mu0 := Measure.isProbabilityMeasure_map hembed.aemeasurable
  letI : ∀ j, IsProbabilityMeasure
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j) :=
    fun j ↦ isProbabilityMeasure_embeddedMarginal candidate A hA next hnext out hout
      roundCost hcost embed hembed rho j
  have htel := adaptiveMarginal_absorbingEvent_eq_sum P mu0
    measurableSet_acceptedStates (measurableSet_acceptedOutputEvent hT)
    (fun _ hz ↦ hz.1) g hg hstep L
  rw [embeddedInitial_acceptedOutputEvent embed hembed hRunning rho hT, zero_add] at htel
  change Arlib.adaptiveMarginal P mu0 L (acceptedOutputEvent T) = _
  rw [htel]
  apply Finset.sum_congr rfl
  intro j hj
  let p := embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho j
  have hpTop : p A ≠ ⊤ := by
    haveI : IsProbabilityMeasure p := by
      unfold p embeddedProposal sampleFromKernel
      letI : IsProbabilityMeasure (condOn
          (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)
          Ttc.FiniteContinuingRetry.runningStates) := Arlib.isProbabilityMeasure_condOn _
        (hs0 j (Finset.mem_range.1 hj)) (measure_ne_top _ _)
      letI : IsProbabilityMeasure ((condOn
          (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)
          Ttc.FiniteContinuingRetry.runningStates).map current) :=
        Measure.isProbabilityMeasure_map measurable_current.aemeasurable
      infer_instance
    exact measure_ne_top p A
  rw [Measure.map_apply hout hT, condOn_apply p hA (hT.preimage hout)]
  change (∫⁻ z in Ttc.FiniteContinuingRetry.runningStates,
      candidate j (current z) (A ∩ out ⁻¹' T)
      ∂(embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)) = _
  rw [← embeddedSurvival_mul_proposal_apply candidate A hA next hnext out hout roundCost
    hcost embed hembed rho j (hs0 j (Finset.mem_range.1 hj))
      (hA.inter (hT.preimage hout))]
  change _ = (_ * p A) * (p (out ⁻¹' T ∩ A) / p A)
  rw [show out ⁻¹' T ∩ A = A ∩ out ⁻¹' T from inter_comm _ _, div_eq_mul_inv]
  have hcanc : p A * (p A)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ha0 j (Finset.mem_range.1 hj)) hpTop
  calc
    _ = (p A * (p A)⁻¹) *
        (embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j *
          p (A ∩ out ⁻¹' T)) := by rw [hcanc, one_mul]
    _ = _ := by ac_rfl

/-- Exact output split into normalized first-hit laws plus the variable unresolved tail. -/
theorem map_output_embeddedMarginal_eq_sum_add_tail
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (hRunning : ∀ x, accepted (embed x) ≠ true)
    (rho : Measure X) [IsProbabilityMeasure rho] (L : Nat)
    (hs0 : ∀ j, j < L → embeddedSurvival candidate A hA next hnext out hout
      roundCost hcost embed rho j ≠ 0)
    (ha0 : ∀ j, j < L → embeddedProposal candidate A hA next hnext out hout
      roundCost hcost embed rho j A ≠ 0) :
    Measure.map output
        (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L) =
      (∑ i : Fin L,
        (embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho i *
          embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho i A) •
        Measure.map out (condOn
          (embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho i) A)) +
      embeddedRunningOutput
        (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L) := by
  letI := isProbabilityMeasure_embeddedMarginal candidate A hA next hnext out hout
    roundCost hcost embed hembed rho L
  ext T hT
  let mu := embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L
  have hunion : (output : RetryState E F → F) ⁻¹' T =
      acceptedOutputEvent (E := E) T ∪
        (Ttc.FiniteContinuingRetry.runningStates ∩ (output : RetryState E F → F) ⁻¹' T) := by
    ext z
    by_cases hz : accepted z = true <;>
      simp [acceptedOutputEvent, Ttc.FiniteContinuingRetry.runningStates,
        acceptedStates, hz]
  have hdisj : Disjoint (acceptedOutputEvent (E := E) T)
      (Ttc.FiniteContinuingRetry.runningStates ∩ (output : RetryState E F → F) ⁻¹' T) :=
    Set.disjoint_left.2 fun _ ha hr ↦ hr.1 ha.1
  rw [Measure.map_apply measurable_output hT, hunion,
    measure_union hdisj
      (Ttc.FiniteContinuingRetry.measurableSet_runningStates.inter
        (hT.preimage measurable_output)), Measure.add_apply,
    embeddedRunningOutput, Measure.map_apply measurable_output hT,
    Measure.restrict_apply (hT.preimage measurable_output), inter_comm]
  have hacc := acceptedOutputEvent_eq_sum_embedded candidate A hA next hnext out hout
    roundCost hcost embed hembed hRunning rho L hs0 ha0 hT
  rw [hacc, ← Fin.sum_univ_eq_sum_range]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

/-- Selective first-hit TV for an arbitrary measurable initial retry-state embedding. -/
theorem tvLe_map_output_embeddedMarginal_selective
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (hRunning : ∀ x, accepted (embed x) ≠ true)
    (rho : Measure X) [IsProbabilityMeasure rho] (L : Nat)
    (target : Measure F) [IsProbabilityMeasure target]
    (eta r acceptedError : ENNReal)
    (hs0 : ∀ j, embeddedSurvival candidate A hA next hnext out hout roundCost hcost
      embed rho j ≠ 0)
    (ha0 : ∀ j, embeddedProposal candidate A hA next hnext out hout roundCost hcost
      embed rho j A ≠ 0)
    (haccepted : ∀ i : Fin L,
      eta ≤ embeddedSurvival candidate A hA next hnext out hout roundCost hcost
        embed rho i →
      TVLe (Measure.map out (condOn
        (embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho i) A))
        target acceptedError)
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤ embeddedSurvival candidate A hA next hnext out hout roundCost
      hcost embed rho j → embeddedProposal candidate A hA next hnext out hout roundCost
        hcost embed rho j Aᶜ ≤ r) :
    TVLe (Measure.map output
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L))
      target (acceptedError + (eta + r ^ L)) := by
  letI : ∀ j, IsProbabilityMeasure
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j) :=
    fun j ↦ isProbabilityMeasure_embeddedMarginal candidate A hA next hnext out hout
      roundCost hcost embed hembed rho j
  let p : Nat → Measure C := fun j ↦
    embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho j
  have hpall : ∀ j, IsProbabilityMeasure (p j) := by
    intro j
    dsimp only [p]
    unfold embeddedProposal sampleFromKernel
    letI : IsProbabilityMeasure (condOn
        (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)
        Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ (hs0 j) (measure_ne_top _ _)
    letI : IsProbabilityMeasure ((condOn
        (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)
        Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    infer_instance
  letI : ∀ j, IsProbabilityMeasure (p j) := hpall
  let w : Fin L → ENNReal := fun i ↦
    embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho i * p i A
  let q : Fin L → Measure F := fun i ↦ Measure.map out (condOn (p i) A)
  let sN : Nat → ENNReal := fun j ↦
    embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j
  have hqprob : ∀ i, IsProbabilityMeasure (q i) := by
    intro i
    dsimp only [q]
    letI : IsProbabilityMeasure (condOn (p i) A) :=
      Arlib.isProbabilityMeasure_condOn _ (by simpa only [p] using ha0 i)
        (measure_ne_top _ _)
    exact Measure.isProbabilityMeasure_map hout.aemeasurable
  letI : ∀ i, IsProbabilityMeasure (q i) := hqprob
  let tail := embeddedRunningOutput
    (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L)
  have hdecomp := map_output_embeddedMarginal_eq_sum_add_tail candidate A hA next hnext
    out hout roundCost hcost embed hembed hRunning rho L (fun j _ ↦ hs0 j)
      (fun j _ ↦ ha0 j)
  have htail : tail Set.univ = sN L := by
    dsimp only [tail]
    rw [embeddedRunningOutput, Measure.map_apply measurable_output MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rfl
  have hmass : (∑ i, w i) + sN L = 1 := by
    have hpart := accepted_add_survival_eq_one
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L)
    have hacc := acceptedOutputEvent_eq_sum_embedded candidate A hA next hnext out hout
      roundCost hcost embed hembed hRunning rho L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j)
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set F))
    rw [hacc, ← Fin.sum_univ_eq_sum_range] at hpart
    simpa only [w, p, q, sN, embeddedSurvival,
      Ttc.FiniteContinuingRetryDecomposition.runningStates,
      Ttc.FiniteContinuingRetry.runningStates, measure_univ, mul_one] using hpart
  have hsbase : sN 0 ≤ 1 := prob_le_one
  have hsmono : ∀ j, sN (j + 1) ≤ sN j := by
    intro j
    dsimp only [sN]
    rw [embeddedSurvival_succ candidate A hA next hnext out hout roundCost hcost embed
      hembed rho j (hs0 j)]
    exact (mul_le_mul_left' prob_le_one _).trans_eq (mul_one _)
  have hscontract : ∀ j, eta ≤ sN j → sN (j + 1) ≤ r * sN j := by
    intro j hj
    dsimp only [sN] at hj ⊢
    rw [embeddedSurvival_succ candidate A hA next hnext out hout roundCost hcost embed
      hembed rho j (hs0 j)]
    simpa only [p, mul_comm] using
      mul_le_mul_left' (hreject j hj)
        (embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j)
  have hrec : ∀ j, j < L →
      (if hj : j < L then w ⟨j, hj⟩ else 0) + sN (j + 1) = sN j := by
    intro j hj
    simp only [hj, dite_true]
    dsimp only [w, sN]
    rw [embeddedSurvival_succ candidate A hA next hnext out hout roundCost hcost embed
      hembed rho j (hs0 j), ← mul_add, prob_add_prob_compl hA, mul_one]
  have hbadN := Ttc.ContinuingRejectionSelective.badWeights_add_survival_le_eta_add_pow
    (fun j ↦ if hj : j < L then w ⟨j, hj⟩ else 0) sN L eta r hrec hsbase hr
      hsmono hscontract
  have hbad : (∑ i ∈ (Finset.univ : Finset (Fin L)).filter
      (fun i : Fin L ↦ ¬ eta ≤ sN (i : Nat)), w i) + sN L ≤ eta + r ^ L := by
    rw [Finset.sum_filter] at hbadN ⊢
    rw [← Fin.sum_univ_eq_sum_range] at hbadN
    simpa using hbadN
  rw [hdecomp]
  apply tvLe_sum_smul_add_tail_selective L w q tail target acceptedError
    (eta + r ^ L) (fun i ↦ eta ≤ sN (i : Nat))
  · simpa [htail] using hmass
  · intro i hi
    simpa only [q, p, sN] using haccepted i hi
  · simpa [htail] using hbad

#print axioms tvLe_map_output_embeddedMarginal_selective

end Ttc.FiniteContinuingRetryEmbeddedSelective
