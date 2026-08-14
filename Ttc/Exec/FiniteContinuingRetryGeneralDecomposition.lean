import Ttc.Exec.FiniteContinuingRetryDecomposition
import Ttc.Volume.CVCombinedContinuingAccept

/-! First-hit mixture decomposition for retry machines with distinct state, candidate,
and output types. -/

namespace Ttc.FiniteContinuingRetryGeneralDecomposition

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryDecomposition
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical BigOperators

variable {E C F : Type*} [MeasurableSpace E] [MeasurableSpace C] [MeasurableSpace F]

noncomputable def schedule
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost) :
    Nat → Kernel (RetryState E F) (RetryState E F) :=
  retryStep candidate A hA next hnext out hout roundCost hcost

instance schedule.isMarkovKernel
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost) (j : Nat) :
    IsMarkovKernel (schedule candidate A hA next hnext out hout roundCost hcost j) := by
  unfold schedule
  infer_instance

noncomputable def initialLaw (x : E) (fallback : F) : Measure (RetryState E F) :=
  Measure.dirac (x, false, fallback, 0)

instance initialLaw.isProbabilityMeasure (x : E) (fallback : F) :
    IsProbabilityMeasure (initialLaw x fallback) := by
  unfold initialLaw
  infer_instance

noncomputable def marginal
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (j : Nat) : Measure (RetryState E F) :=
  Arlib.adaptiveMarginal (schedule candidate A hA next hnext out hout roundCost hcost)
    (initialLaw x fallback) j

instance marginal.isProbabilityMeasure
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (j : Nat) :
    IsProbabilityMeasure
      (marginal candidate A hA next hnext out hout roundCost hcost x fallback j) := by
  unfold marginal
  infer_instance

noncomputable def survival
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (j : Nat) : ENNReal :=
  marginal candidate A hA next hnext out hout roundCost hcost x fallback j
    Ttc.FiniteContinuingRetry.runningStates

/-- Candidate law at retry `j`, conditional on the actual execution surviving to `j`. -/
noncomputable def proposal
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (j : Nat) : Measure C :=
  sampleFromKernel (candidate j)
    ((Arlib.condOn
      (marginal candidate A hA next hnext out hout roundCost hcost x fallback j)
      Ttc.FiniteContinuingRetry.runningStates).map current)

theorem survival_mul_proposal_apply
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (j : Nat)
    (hs0 : survival candidate A hA next hnext out hout roundCost hcost x fallback j ≠ 0)
    {B : Set C} (hB : MeasurableSet B) :
    survival candidate A hA next hnext out hout roundCost hcost x fallback j *
        proposal candidate A hA next hnext out hout roundCost hcost x fallback j B =
      ∫⁻ s in Ttc.FiniteContinuingRetry.runningStates, candidate j (current s) B
        ∂(marginal candidate A hA next hnext out hout roundCost hcost x fallback j) := by
  let rho := marginal candidate A hA next hnext out hout roundCost hcost x fallback j
  let sv := survival candidate A hA next hnext out hout roundCost hcost x fallback j
  let I := ∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
    candidate j (current s) B ∂rho
  have hstop : sv ≠ ⊤ := measure_ne_top rho Ttc.FiniteContinuingRetry.runningStates
  have hp : proposal candidate A hA next hnext out hout roundCost hcost x fallback j B =
      sv⁻¹ * I := by
    unfold proposal sampleFromKernel
    rw [Measure.bind_apply hB (candidate j).aemeasurable,
      lintegral_map ((candidate j).measurable_coe hB) measurable_current,
      Arlib.condOn_def, lintegral_smul_measure]
    rfl
  rw [hp]
  exact ENNReal.mul_inv_cancel_left hs0 hstop

/-- Accepted increment equals the actual first-hit weight times the mapped normalized
candidate law. -/
theorem accepted_increment_eq_weight_mul
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (j : Nat)
    (hs0 : survival candidate A hA next hnext out hout roundCost hcost x fallback j ≠ 0)
    (ha0 : proposal candidate A hA next hnext out hout roundCost hcost x fallback j A ≠ 0)
    {T : Set F} (hT : MeasurableSet T) :
    (∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
      candidate j (current s) (A ∩ out ⁻¹' T)
      ∂(marginal candidate A hA next hnext out hout roundCost hcost x fallback j)) =
      (survival candidate A hA next hnext out hout roundCost hcost x fallback j *
        proposal candidate A hA next hnext out hout roundCost hcost x fallback j A) *
      (Measure.map out
        (Arlib.condOn
          (proposal candidate A hA next hnext out hout roundCost hcost x fallback j) A)) T := by
  let p := proposal candidate A hA next hnext out hout roundCost hcost x fallback j
  have hptop : p A ≠ ⊤ := by
    haveI : IsProbabilityMeasure p := by
      unfold p proposal sampleFromKernel
      letI : IsProbabilityMeasure
          (Arlib.condOn
            (marginal candidate A hA next hnext out hout roundCost hcost x fallback j)
            Ttc.FiniteContinuingRetry.runningStates) :=
        Arlib.isProbabilityMeasure_condOn _ hs0 (measure_ne_top _ _)
      letI : IsProbabilityMeasure
          ((Arlib.condOn
            (marginal candidate A hA next hnext out hout roundCost hcost x fallback j)
            Ttc.FiniteContinuingRetry.runningStates).map current) :=
        Measure.isProbabilityMeasure_map measurable_current.aemeasurable
      infer_instance
    exact measure_ne_top p A
  rw [Measure.map_apply hout hT, Arlib.condOn_apply p hA (hT.preimage hout)]
  rw [← survival_mul_proposal_apply candidate A hA next hnext out hout roundCost hcost
    x fallback j hs0 (hA.inter (hT.preimage hout))]
  change _ = (_ * p A) * (p (out ⁻¹' T ∩ A) / p A)
  rw [show out ⁻¹' T ∩ A = A ∩ out ⁻¹' T from inter_comm _ _, div_eq_mul_inv]
  have hcancel : p A * (p A)⁻¹ = 1 := ENNReal.mul_inv_cancel ha0 hptop
  calc
    _ = (p A * (p A)⁻¹) *
        (survival candidate A hA next hnext out hout roundCost hcost x fallback j *
          p (A ∩ out ⁻¹' T)) := by rw [hcancel, one_mul]
    _ = _ := by ac_rfl

/-- Exact survival recurrence for the general retry machine. -/
theorem survival_succ
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (j : Nat)
    (hs0 : survival candidate A hA next hnext out hout roundCost hcost x fallback j ≠ 0) :
    survival candidate A hA next hnext out hout roundCost hcost x fallback (j + 1) =
      survival candidate A hA next hnext out hout roundCost hcost x fallback j *
        proposal candidate A hA next hnext out hout roundCost hcost x fallback j Aᶜ := by
  unfold survival marginal
  rw [Arlib.adaptiveMarginal]
  rw [Measure.bind_apply Ttc.FiniteContinuingRetry.measurableSet_runningStates
    (schedule candidate A hA next hnext out hout roundCost hcost j).aemeasurable]
  have hfun : (fun s : RetryState E F ↦
      schedule candidate A hA next hnext out hout roundCost hcost j s
        Ttc.FiniteContinuingRetry.runningStates) =
      Ttc.FiniteContinuingRetry.runningStates.indicator
        (fun s ↦ candidate j (current s) Aᶜ) := by
    funext s
    rw [schedule, retryStep_runningStates]
    by_cases hs : accepted s = true
    · simp [hs, Ttc.FiniteContinuingRetry.runningStates, acceptedStates]
    · simp [hs, Ttc.FiniteContinuingRetry.runningStates, acceptedStates]
  rw [hfun]
  rw [lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
  simpa only [survival, marginal] using
    (survival_mul_proposal_apply candidate A hA next hnext out hout roundCost hcost
      x fallback j hs0 hA.compl).symm

/-- Accepted output mass telescopes into the mapped normalized candidate laws with their
actual first-hit weights. -/
theorem acceptedOutputEvent_eq_sum
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (L : Nat)
    (hs0 : ∀ j, j < L →
      survival candidate A hA next hnext out hout roundCost hcost x fallback j ≠ 0)
    (ha0 : ∀ j, j < L →
      proposal candidate A hA next hnext out hout roundCost hcost x fallback j A ≠ 0)
    {T : Set F} (hT : MeasurableSet T) :
    marginal candidate A hA next hnext out hout roundCost hcost x fallback L
        (acceptedOutputEvent T) =
      ∑ j ∈ Finset.range L,
        (survival candidate A hA next hnext out hout roundCost hcost x fallback j *
          proposal candidate A hA next hnext out hout roundCost hcost x fallback j A) *
        (Measure.map out
          (Arlib.condOn
            (proposal candidate A hA next hnext out hout roundCost hcost x fallback j) A)) T := by
  let P := schedule candidate A hA next hnext out hout roundCost hcost
  let mu0 := initialLaw x fallback
  let g : Nat → RetryState E F → ENNReal := fun j s ↦
    candidate j (current s) (A ∩ out ⁻¹' T)
  have hg : ∀ j, Measurable (g j) := fun j ↦
    ((candidate j).measurable_coe (hA.inter (hT.preimage hout))).comp measurable_current
  have hstep : ∀ j s, P j s (acceptedOutputEvent T) =
      if s ∈ (acceptedStates : Set (RetryState E F)) then
        (acceptedOutputEvent T).indicator (fun _ ↦ (1 : ENNReal)) s else g j s := by
    intro j s
    dsimp only [P]
    have hh := retryStep_acceptedOutputEvent candidate A hA next hnext out hout
      roundCost hcost j s hT
    rw [schedule, hh]
    by_cases hs : accepted s = true
    · simp only [hs, if_pos]
      by_cases ht : s ∈ acceptedOutputEvent T <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht, acceptedStates, hs]
    · simp [hs, acceptedStates, g]
  have htel := adaptiveMarginal_absorbingEvent_eq_sum P mu0
    measurableSet_acceptedStates (measurableSet_acceptedOutputEvent hT)
    (fun _ hs ↦ hs.1) g hg hstep L
  have hinit : mu0 (acceptedOutputEvent T) = 0 := by
    dsimp only [mu0]
    rw [initialLaw, Measure.dirac_apply' _ (measurableSet_acceptedOutputEvent hT)]
    simp [acceptedOutputEvent, accepted]
  rw [hinit, zero_add] at htel
  change Arlib.adaptiveMarginal P mu0 L (acceptedOutputEvent T) = _
  rw [htel]
  apply Finset.sum_congr rfl
  intro j hj
  exact accepted_increment_eq_weight_mul candidate A hA next hnext out hout roundCost hcost
    x fallback j (hs0 j (Finset.mem_range.1 hj)) (ha0 j (Finset.mem_range.1 hj)) hT

/-- End-to-end TV theorem for the actual finite retry state machine.  Candidate, current
state, and accepted output may have different types. -/
theorem tvLe_cutoffOutput_of_eighth
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (L : Nat)
    (tau : Measure C) [IsProbabilityMeasure tau]
    (eta r zeta : ENNReal)
    (hs0 : ∀ j,
      survival candidate A hA next hnext out hout roundCost hcost x fallback j ≠ 0)
    (ha0 : ∀ j,
      proposal candidate A hA next hnext out hout roundCost hcost x fallback j A ≠ 0)
    (hcandidate : ∀ i : Fin L,
      Arlib.TVLe
        (proposal candidate A hA next hnext out hout roundCost hcost x fallback i) tau zeta)
    (heighth : ENNReal.ofReal (1 / 8 : Real) ≤ tau A)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤
      survival candidate A hA next hnext out hout roundCost hcost x fallback j →
      proposal candidate A hA next hnext out hout roundCost hcost x fallback j Aᶜ ≤ r) :
    Arlib.TVLe
      (Measure.map (cutoffOutput (E := E) fallback)
        (marginal candidate A hA next hnext out hout roundCost hcost x fallback L))
      (Measure.map out (Arlib.condOn tau A))
      (32 * zeta + (eta + r ^ L)) := by
  let p : Nat → Measure C := fun j ↦
    proposal candidate A hA next hnext out hout roundCost hcost x fallback j
  have hpall : ∀ j, IsProbabilityMeasure (p j) := by
    intro j
    dsimp only [p]
    unfold proposal sampleFromKernel
    letI : IsProbabilityMeasure
        (Arlib.condOn
          (marginal candidate A hA next hnext out hout roundCost hcost x fallback j)
          Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ (hs0 j) (measure_ne_top _ _)
    letI : IsProbabilityMeasure
        ((Arlib.condOn
          (marginal candidate A hA next hnext out hout roundCost hcost x fallback j)
          Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    infer_instance
  letI : ∀ j, IsProbabilityMeasure (p j) := hpall
  let w : Fin L → ENNReal := fun i ↦
    survival candidate A hA next hnext out hout roundCost hcost x fallback i * p i A
  let q : Fin L → Measure F := fun i ↦ Measure.map out (Arlib.condOn (p i) A)
  let s : Nat → ENNReal := fun j ↦
    survival candidate A hA next hnext out hout roundCost hcost x fallback j
  have hqprob : ∀ i, IsProbabilityMeasure (q i) := by
    intro i
    dsimp only [q]
    letI : IsProbabilityMeasure (Arlib.condOn (p i) A) :=
      Arlib.isProbabilityMeasure_condOn _ (by simpa only [p] using ha0 i)
        (measure_ne_top _ _)
    exact Measure.isProbabilityMeasure_map hout.aemeasurable
  letI : ∀ i, IsProbabilityMeasure (q i) := hqprob
  have houtEq : Measure.map (cutoffOutput (E := E) fallback)
      (marginal candidate A hA next hnext out hout roundCost hcost x fallback L) =
      Ttc.ContinuingRejectionSignificant.acceptedMixture L w q (s L) fallback := by
    apply map_cutoffOutput_eq_acceptedMixture_of_apply
    intro T hT
    have hacc := acceptedOutputEvent_eq_sum candidate A hA next hnext out hout roundCost hcost
      x fallback L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j) hT
    rw [← Fin.sum_univ_eq_sum_range] at hacc
    simpa only [w, q, p, s] using hacc
  have hmass : (∑ i, w i) + s L = 1 := by
    have hpart := accepted_add_survival_eq_one
      (marginal candidate A hA next hnext out hout roundCost hcost x fallback L)
    have hacc := acceptedOutputEvent_eq_sum candidate A hA next hnext out hout roundCost hcost
      x fallback L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j)
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set F))
    rw [hacc, ← Fin.sum_univ_eq_sum_range] at hpart
    simpa only [w, q, p, s, survival,
      Ttc.FiniteContinuingRetryDecomposition.runningStates,
      Ttc.FiniteContinuingRetry.runningStates, measure_univ, mul_one] using hpart
  have hsbase : s 0 ≤ 1 := prob_le_one
  have hsmono : ∀ j, s (j + 1) ≤ s j := by
    intro j
    dsimp only [s]
    rw [survival_succ candidate A hA next hnext out hout roundCost hcost x fallback j (hs0 j)]
    calc
      _ ≤ survival candidate A hA next hnext out hout roundCost hcost x fallback j * 1 :=
        mul_le_mul_left' prob_le_one _
      _ = _ := mul_one _
  have hscontract : ∀ j, eta ≤ s j → s (j + 1) ≤ r * s j := by
    intro j hj
    dsimp only [s] at hj ⊢
    rw [survival_succ candidate A hA next hnext out hout roundCost hcost x fallback j (hs0 j)]
    simpa only [p, mul_comm] using
      (mul_le_mul_left' (hreject j hj)
        (survival candidate A hA next hnext out hout roundCost hcost x fallback j))
  have htail := Ttc.ContinuingRejectionSignificant.survival_le_eta_add_pow
    s hsbase hr hsmono hscontract L
  have htauPos : tau A ≠ 0 := ne_of_gt <|
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) heighth
  letI : IsProbabilityMeasure (Arlib.condOn tau A) :=
    Arlib.isProbabilityMeasure_condOn _ htauPos (measure_ne_top tau A)
  letI : IsProbabilityMeasure (Measure.map out (Arlib.condOn tau A)) :=
    Measure.isProbabilityMeasure_map hout.aemeasurable
  have hqTV : ∀ i, Arlib.TVLe (q i)
      (Measure.map out (Arlib.condOn tau A)) (32 * zeta) := by
    intro i
    dsimp only [q]
    exact (Ttc.ContinuingRejectionSignificant.tvLe_condOn_eighth
      (p i) tau hA (by simpa only [p] using hcandidate i) heighth hzeta).map hout
  rw [houtEq]
  have hbase := Ttc.ContinuingRejectionSignificant.tvLe_acceptedMixture
    L w q (Measure.map out (Arlib.condOn tau A)) (s L) (32 * zeta) fallback hmass hqTV
  exact hbase.mono (by gcongr)

/-- Core form used when only an observable of each candidate (for example, candidate with
recorded cost erased) is close to the ideal accepted-output law. -/
theorem tvLe_cutoffOutput_of_accepted
    (candidate : Nat → Kernel E C) [∀ j : Nat, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (x : E) (fallback : F) (L : Nat)
    (target : Measure F) [IsProbabilityMeasure target]
    (eta r acceptedError : ENNReal)
    (hs0 : ∀ j,
      survival candidate A hA next hnext out hout roundCost hcost x fallback j ≠ 0)
    (ha0 : ∀ j,
      proposal candidate A hA next hnext out hout roundCost hcost x fallback j A ≠ 0)
    (haccepted : ∀ i : Fin L,
      Arlib.TVLe
        (Measure.map out (Arlib.condOn
          (proposal candidate A hA next hnext out hout roundCost hcost x fallback i) A))
        target acceptedError)
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤
      survival candidate A hA next hnext out hout roundCost hcost x fallback j →
      proposal candidate A hA next hnext out hout roundCost hcost x fallback j Aᶜ ≤ r) :
    Arlib.TVLe
      (Measure.map (cutoffOutput (E := E) fallback)
        (marginal candidate A hA next hnext out hout roundCost hcost x fallback L))
      target (acceptedError + (eta + r ^ L)) := by
  let p : Nat → Measure C := fun j ↦
    proposal candidate A hA next hnext out hout roundCost hcost x fallback j
  have hpall : ∀ j, IsProbabilityMeasure (p j) := by
    intro j
    dsimp only [p]
    unfold proposal sampleFromKernel
    letI : IsProbabilityMeasure
        (Arlib.condOn
          (marginal candidate A hA next hnext out hout roundCost hcost x fallback j)
          Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ (hs0 j) (measure_ne_top _ _)
    letI : IsProbabilityMeasure
        ((Arlib.condOn
          (marginal candidate A hA next hnext out hout roundCost hcost x fallback j)
          Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    infer_instance
  letI : ∀ j, IsProbabilityMeasure (p j) := hpall
  let w : Fin L → ENNReal := fun i ↦
    survival candidate A hA next hnext out hout roundCost hcost x fallback i * p i A
  let q : Fin L → Measure F := fun i ↦ Measure.map out (Arlib.condOn (p i) A)
  let s : Nat → ENNReal := fun j ↦
    survival candidate A hA next hnext out hout roundCost hcost x fallback j
  have hqprob : ∀ i, IsProbabilityMeasure (q i) := by
    intro i
    dsimp only [q]
    letI : IsProbabilityMeasure (Arlib.condOn (p i) A) :=
      Arlib.isProbabilityMeasure_condOn _ (by simpa only [p] using ha0 i)
        (measure_ne_top _ _)
    exact Measure.isProbabilityMeasure_map hout.aemeasurable
  letI : ∀ i, IsProbabilityMeasure (q i) := hqprob
  have houtEq : Measure.map (cutoffOutput (E := E) fallback)
      (marginal candidate A hA next hnext out hout roundCost hcost x fallback L) =
      Ttc.ContinuingRejectionSignificant.acceptedMixture L w q (s L) fallback := by
    apply map_cutoffOutput_eq_acceptedMixture_of_apply
    intro T hT
    have hacc := acceptedOutputEvent_eq_sum candidate A hA next hnext out hout roundCost hcost
      x fallback L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j) hT
    rw [← Fin.sum_univ_eq_sum_range] at hacc
    simpa only [w, q, p, s] using hacc
  have hmass : (∑ i, w i) + s L = 1 := by
    have hpart := accepted_add_survival_eq_one
      (marginal candidate A hA next hnext out hout roundCost hcost x fallback L)
    have hacc := acceptedOutputEvent_eq_sum candidate A hA next hnext out hout roundCost hcost
      x fallback L (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j)
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set F))
    rw [hacc, ← Fin.sum_univ_eq_sum_range] at hpart
    simpa only [w, q, p, s, survival,
      Ttc.FiniteContinuingRetryDecomposition.runningStates,
      Ttc.FiniteContinuingRetry.runningStates, measure_univ, mul_one] using hpart
  have hsbase : s 0 ≤ 1 := prob_le_one
  have hsmono : ∀ j, s (j + 1) ≤ s j := by
    intro j
    dsimp only [s]
    rw [survival_succ candidate A hA next hnext out hout roundCost hcost x fallback j (hs0 j)]
    calc
      _ ≤ survival candidate A hA next hnext out hout roundCost hcost x fallback j * 1 :=
        mul_le_mul_left' prob_le_one _
      _ = _ := mul_one _
  have hscontract : ∀ j, eta ≤ s j → s (j + 1) ≤ r * s j := by
    intro j hj
    dsimp only [s] at hj ⊢
    rw [survival_succ candidate A hA next hnext out hout roundCost hcost x fallback j (hs0 j)]
    simpa only [p, mul_comm] using
      (mul_le_mul_left' (hreject j hj)
        (survival candidate A hA next hnext out hout roundCost hcost x fallback j))
  have htail := Ttc.ContinuingRejectionSignificant.survival_le_eta_add_pow
    s hsbase hr hsmono hscontract L
  rw [houtEq]
  have hbase := Ttc.ContinuingRejectionSignificant.tvLe_acceptedMixture
    L w q target (s L) acceptedError fallback hmass (by
      intro i
      simpa only [q, p] using haccepted i)
  exact hbase.mono (by gcongr)

#print axioms survival_mul_proposal_apply
#print axioms accepted_increment_eq_weight_mul
#print axioms survival_succ
#print axioms acceptedOutputEvent_eq_sum
#print axioms tvLe_cutoffOutput_of_eighth
#print axioms tvLe_cutoffOutput_of_accepted

end Ttc.FiniteContinuingRetryGeneralDecomposition
