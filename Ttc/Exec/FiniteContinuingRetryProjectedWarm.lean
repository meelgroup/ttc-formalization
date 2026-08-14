import Ttc.Exec.FiniteContinuingRetryEmbeddedSelective
import Ttc.Exec.FiniteContinuingRetrySelfCurrentWarm
import Ttc.Exec.FiniteContinuingRetryRandomFallback
import Ttc.Volume.CVFiniteRetryWarmFallback

/-! Warmness of a projected accepted sublaw for an embedded finite retry machine. -/

namespace Ttc.FiniteContinuingRetryProjectedWarm

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGeneralDecomposition
open Ttc.FiniteContinuingRetryEmbeddedSelective
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.FiniteContinuingRetrySelfCurrentWarm
open scoped ENNReal Classical BigOperators

variable {X E C F G : Type*}
  [MeasurableSpace X] [MeasurableSpace E] [MeasurableSpace C]
  [MeasurableSpace F] [MeasurableSpace G]

/-- Unnormalised law of the current point on the still-running branch. -/
noncomputable def runningCurrent (mu : Measure (RetryState E F)) : Measure E :=
  Measure.map current (mu.restrict Ttc.FiniteContinuingRetry.runningStates)

/-- Accepted killed transition, followed only by the projection needed by the next phase. -/
noncomputable def acceptedProjectedKernel
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A) (seed : C → G) (hseed : Measurable seed)
    (j : Nat) : Kernel E G :=
  Kernel.map ((candidate j).restrict hA) seed

/-- The unnormalised projected first-hit contribution at retry `j`. -/
noncomputable def projectedFirstHitIncrement
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (rho : Measure X)
    (seed : C → G) (hseed : Measurable seed) (j : Nat) : Measure G :=
  sampleFromKernel (acceptedProjectedKernel candidate A hA seed hseed j)
    (runningCurrent
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j))

theorem runningCurrent_embeddedMarginal_succ
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (rho : Measure X) [IsProbabilityMeasure rho] (j : Nat) :
    runningCurrent
        (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho (j + 1)) =
      (runningCurrent
        (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)).bind
          (rejectedKernel candidate A hA next hnext j) := by
  ext T hT
  let mu := embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j
  rw [runningCurrent, Measure.map_apply measurable_current hT,
    Measure.restrict_apply (hT.preimage measurable_current)]
  change Arlib.adaptiveMarginal
      (schedule candidate A hA next hnext out hout roundCost hcost)
      (Measure.map embed rho) (j + 1)
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
  · have hzrun : z ∉ (Ttc.FiniteContinuingRetry.runningStates : Set (RetryState E F)) := by
      simpa [Ttc.FiniteContinuingRetry.runningStates, acceptedStates] using hz
    rw [Set.indicator_of_notMem hzrun]
    rw [schedule, retryStep_apply, if_pos hz,
      Measure.dirac_apply' _
        ((hT.preimage measurable_current).inter
          Ttc.FiniteContinuingRetry.measurableSet_runningStates)]
    simp [hz, Ttc.FiniteContinuingRetry.runningStates, acceptedStates]
  · have hzrun : z ∈ (Ttc.FiniteContinuingRetry.runningStates : Set (RetryState E F)) := by
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

theorem isWarm_runningCurrent_embeddedMarginal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (rho : Measure X) [IsProbabilityMeasure rho] (pi : Measure E) {M : ENNReal}
    (hzero : IsWarm M
      (runningCurrent (Measure.map embed rho)) pi)
    (hreject : ∀ j, pi.bind (rejectedKernel candidate A hA next hnext j) ≤ pi) :
    ∀ j, IsWarm M
      (runningCurrent
        (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)) pi := by
  intro j
  induction j with
  | zero => simpa [embeddedMarginal, Arlib.adaptiveMarginal] using hzero
  | succ j ih =>
      rw [runningCurrent_embeddedMarginal_succ candidate A hA next hnext out hout
        roundCost hcost embed hembed rho j]
      exact (ih.bind (rejectedKernel candidate A hA next hnext j)).trans
        (IsWarm.of_le (hreject j) (IsWarm.refl pi)) |>.mono (by simp)

theorem map_seed_acceptedOutputSubmeasure_eq_sum_projectedFirstHit
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (hRunning : ∀ x, accepted (embed x) ≠ true)
    (rho : Measure X) [IsProbabilityMeasure rho]
    (seedOut : F → G) (hseedOut : Measurable seedOut) (L : Nat) :
    Measure.map seedOut
        (acceptedOutputSubmeasure
          (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L)) =
      ∑ i : Fin L, projectedFirstHitIncrement candidate A hA next hnext out hout
        roundCost hcost embed rho (seedOut ∘ out) (hseedOut.comp hout) i := by
  ext T hT
  let P := schedule candidate A hA next hnext out hout roundCost hcost
  let mu0 := Measure.map embed rho
  let g : Nat → RetryState E F → ENNReal := fun j z ↦
    candidate j (current z) (A ∩ (seedOut ∘ out) ⁻¹' T)
  have hg : ∀ j, Measurable (g j) := fun j ↦
    ((candidate j).measurable_coe (hA.inter
      (hT.preimage (hseedOut.comp hout)))).comp measurable_current
  have hstep : ∀ j z, P j z (acceptedOutputEvent (seedOut ⁻¹' T)) =
      if z ∈ (acceptedStates : Set (RetryState E F)) then
        (acceptedOutputEvent (seedOut ⁻¹' T)).indicator (fun _ ↦ (1 : ENNReal)) z
      else g j z := by
    intro j z
    dsimp only [P]
    rw [schedule, retryStep_acceptedOutputEvent candidate A hA next hnext out hout
      roundCost hcost j z (hT.preimage hseedOut)]
    by_cases hz : accepted z = true
    · simp only [hz, if_pos]
      by_cases ht : z ∈ acceptedOutputEvent (seedOut ⁻¹' T) <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht, acceptedStates, hz]
    · simp only [hz, if_false]
      have hz' : z ∉ (acceptedStates : Set (RetryState E F)) := by
        simpa [acceptedStates] using hz
      rw [if_neg hz']
      change candidate j (current z) (A ∩ out ⁻¹' (seedOut ⁻¹' T)) = _
      rfl
  letI : IsProbabilityMeasure mu0 :=
    Measure.isProbabilityMeasure_map hembed.aemeasurable
  have htel :=
    Ttc.FiniteContinuingRetryDecomposition.adaptiveMarginal_absorbingEvent_eq_sum
      P mu0 measurableSet_acceptedStates
      (measurableSet_acceptedOutputEvent (hT.preimage hseedOut))
      (fun _ hz ↦ hz.1) g hg hstep L
  have hinit : mu0 (acceptedOutputEvent (seedOut ⁻¹' T)) = 0 :=
    embeddedInitial_acceptedOutputEvent embed hembed hRunning rho (hT.preimage hseedOut)
  rw [hinit, zero_add] at htel
  rw [Measure.map_apply hseedOut hT, acceptedOutputSubmeasure,
    Measure.map_apply measurable_output (hT.preimage hseedOut),
    Measure.restrict_apply ((hT.preimage hseedOut).preimage measurable_output)]
  change Arlib.adaptiveMarginal P mu0 L
      (output ⁻¹' (seedOut ⁻¹' T) ∩ acceptedStates) = _
  have hevent : (output : RetryState E F → F) ⁻¹' (seedOut ⁻¹' T) ∩
      (acceptedStates : Set (RetryState E F)) =
      acceptedOutputEvent (E := E) (seedOut ⁻¹' T) := by
    ext z
    constructor
    · rintro ⟨hzT, hza⟩
      exact ⟨hza, hzT⟩
    · rintro ⟨hza, hzT⟩
      exact ⟨hzT, hza⟩
  rw [hevent, htel]
  rw [Measure.finsetSum_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [projectedFirstHitIncrement, sampleFromKernel,
    Measure.bind_apply hT
      (acceptedProjectedKernel candidate A hA (seedOut ∘ out) (hseedOut.comp hout) i).aemeasurable,
    runningCurrent,
    lintegral_map
      ((acceptedProjectedKernel candidate A hA (seedOut ∘ out)
        (hseedOut.comp hout) i).measurable_coe hT) measurable_current,
    ← lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
  change (∫⁻ z in Ttc.FiniteContinuingRetry.runningStates,
      candidate i (current z) (A ∩ (seedOut ∘ out) ⁻¹' T)
      ∂(embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho i)) = _
  rw [lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
  apply setLIntegral_congr_fun Ttc.FiniteContinuingRetry.measurableSet_runningStates
  intro z
  intro _
  change candidate i (current z) (A ∩ (seedOut ∘ out) ⁻¹' T) =
    (Kernel.map ((candidate i).restrict hA) (seedOut ∘ out))
      (current z) T
  rw [Kernel.map_apply _ (hseedOut.comp hout),
    Measure.map_apply (hseedOut.comp hout) hT,
    Kernel.restrict_apply' (candidate i) hA _
      (hT.preimage (hseedOut.comp hout))]
  rw [inter_comm]

/-- Normalized first-hit decomposition of the accepted submeasure alone. -/
theorem acceptedOutputSubmeasure_eq_sum_embedded
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
    acceptedOutputSubmeasure
        (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L) =
      ∑ i : Fin L,
        (embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho i *
          embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho i A) •
        Measure.map out (condOn
          (embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho i) A) := by
  ext T hT
  rw [acceptedOutputSubmeasure, Measure.map_apply measurable_output hT,
    Measure.restrict_apply (hT.preimage measurable_output)]
  have hevent : (output : RetryState E F → F) ⁻¹' T ∩ acceptedStates =
      acceptedOutputEvent (E := E) T := by
    ext z
    constructor
    · rintro ⟨hzT, hza⟩
      exact ⟨hza, hzT⟩
    · rintro ⟨hza, hzT⟩
      exact ⟨hzT, hza⟩
  rw [hevent, acceptedOutputEvent_eq_sum_embedded candidate A hA next hnext out hout
    roundCost hcost embed hembed hRunning rho L hs0 ha0 hT,
    ← Fin.sum_univ_eq_sum_range]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

/-- Selective first-hit TV followed by an arbitrary independent fallback on the unresolved
branch.  The fallback itself needs no accuracy property because its whole mass is charged. -/
theorem tvLe_randomFallback_embeddedMarginal_selective
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (hRunning : ∀ x, accepted (embed x) ≠ true)
    (rho : Measure X) [IsProbabilityMeasure rho] (L : Nat)
    (fallback target : Measure F)
    [IsProbabilityMeasure fallback] [IsProbabilityMeasure target]
    (eta r acceptedError : ENNReal)
    (hs0 : ∀ j, embeddedSurvival candidate A hA next hnext out hout roundCost hcost
      embed rho j ≠ 0)
    (ha0 : ∀ j, embeddedProposal candidate A hA next hnext out hout roundCost hcost
      embed rho j A ≠ 0)
    (haccepted : ∀ i : Fin L,
      eta ≤ embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho i →
      TVLe (Measure.map out (condOn
        (embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho i) A))
        target acceptedError)
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤ embeddedSurvival candidate A hA next hnext out hout roundCost
      hcost embed rho j → embeddedProposal candidate A hA next hnext out hout roundCost
        hcost embed rho j Aᶜ ≤ r) :
    TVLe (sampleFromKernel (randomFallbackKernel fallback)
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
  let muL := embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L
  have hdecomp : acceptedOutputSubmeasure muL = ∑ i, w i • q i := by
    simpa only [muL, w, q, p] using
      acceptedOutputSubmeasure_eq_sum_embedded candidate A hA next hnext out hout
        roundCost hcost embed hembed hRunning rho L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j)
  have hmass : (∑ i, w i) + muL Ttc.FiniteContinuingRetry.runningStates = 1 := by
    have hpart := Ttc.FiniteContinuingRetryDecomposition.accepted_add_survival_eq_one muL
    have hacc := acceptedOutputEvent_eq_sum_embedded candidate A hA next hnext out hout
      roundCost hcost embed hembed hRunning rho L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j)
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set F))
    rw [hacc, ← Fin.sum_univ_eq_sum_range] at hpart
    simpa only [muL, w, p, sN, embeddedSurvival,
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
  apply tvLe_sampleFrom_randomFallbackKernel_selective muL fallback target L w q
    acceptedError (eta + r ^ L) (fun i ↦ eta ≤ sN (i : Nat)) hdecomp hmass
  · intro i hi
    simpa only [q, p, sN] using haccepted i hi
  · simpa only [muL, sN, embeddedSurvival] using hbad

/-- Uniform projected first-hit warmth: rejected killed transitions retain the incoming
warmness, accepted killed transitions cost `Cwarm`, and summing `L` retries costs `L`. -/
theorem isWarm_map_seed_acceptedOutputSubmeasure
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (hRunning : ∀ x, accepted (embed x) ≠ true)
    (rho : Measure X) [IsProbabilityMeasure rho]
    (seedOut : F → G) (hseedOut : Measurable seedOut)
    (pi : Measure E) (target : Measure G) (L : Nat) {M Cwarm : ENNReal}
    (hzero : IsWarm M (runningCurrent (Measure.map embed rho)) pi)
    (hreject : ∀ j, pi.bind (rejectedKernel candidate A hA next hnext j) ≤ pi)
    (haccept : ∀ j, IsWarm Cwarm
      (pi.bind (acceptedProjectedKernel candidate A hA (seedOut ∘ out)
        (hseedOut.comp hout) j)) target) :
    IsWarm ((L : ENNReal) * (Cwarm * M))
      (Measure.map seedOut
        (acceptedOutputSubmeasure
          (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L)))
      target := by
  rw [map_seed_acceptedOutputSubmeasure_eq_sum_projectedFirstHit candidate A hA next hnext
    out hout roundCost hcost embed hembed hRunning rho seedOut hseedOut L]
  have hrunning := isWarm_runningCurrent_embeddedMarginal candidate A hA next hnext out hout
    roundCost hcost embed hembed rho pi hzero hreject
  have hinc : ∀ i : Fin L, IsWarm (Cwarm * M)
      (projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
        embed rho (seedOut ∘ out) (hseedOut.comp hout) i) target := by
    intro i
    have hstep := (hrunning i).bind
      (acceptedProjectedKernel candidate A hA (seedOut ∘ out) (hseedOut.comp hout) i)
    exact hstep.trans (haccept i) |>.mono (by rw [mul_comm])
  simpa using Arlib.isWarm_sum
    (fun i : Fin L ↦ projectedFirstHitIncrement candidate A hA next hnext out hout
      roundCost hcost embed rho (seedOut ∘ out) (hseedOut.comp hout) i)
    (fun _ : Fin L ↦ Cwarm * M) target hinc

#print axioms runningCurrent_embeddedMarginal_succ
#print axioms map_seed_acceptedOutputSubmeasure_eq_sum_projectedFirstHit
#print axioms acceptedOutputSubmeasure_eq_sum_embedded
#print axioms tvLe_randomFallback_embeddedMarginal_selective
#print axioms isWarm_map_seed_acceptedOutputSubmeasure

end Ttc.FiniteContinuingRetryProjectedWarm
