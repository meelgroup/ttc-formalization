import Ttc.Exec.FiniteContinuingRetryDecomposition

/-! Concrete mixture decomposition of the finite continuing-retry kernel. -/

namespace Ttc.FiniteContinuingRetryConcreteDecomposition

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryDecomposition
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical BigOperators

variable {X : Type*} [MeasurableSpace X]

noncomputable def schedule
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost) :
    Nat → Kernel (RetryState X X) (RetryState X X) :=
  retryStep candidate A hA id measurable_id id measurable_id roundCost hcost

instance schedule.isMarkovKernel
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost) (j : Nat) :
    IsMarkovKernel (schedule candidate A hA roundCost hcost j) := by
  unfold schedule
  infer_instance

noncomputable def initialLaw (x fallback : X) : Measure (RetryState X X) :=
  Measure.dirac (x, false, fallback, 0)

instance initialLaw.isProbabilityMeasure (x fallback : X) :
    IsProbabilityMeasure (initialLaw x fallback) := by
  unfold initialLaw
  infer_instance

noncomputable def marginal
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost)
    (x fallback : X) (j : Nat) : Measure (RetryState X X) :=
  Arlib.adaptiveMarginal (schedule candidate A hA roundCost hcost)
    (initialLaw x fallback) j

instance marginal.isProbabilityMeasure
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost)
    (x fallback : X) (j : Nat) :
    IsProbabilityMeasure (marginal candidate A hA roundCost hcost x fallback j) := by
  unfold marginal
  infer_instance

noncomputable def survival
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost)
    (x fallback : X) (j : Nat) : ENNReal :=
  marginal candidate A hA roundCost hcost x fallback j
    (Ttc.FiniteContinuingRetry.runningStates : Set (RetryState X X))

/-- Candidate law at retry `j`, conditional on the execution still running. -/
noncomputable def proposal
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost)
    (x fallback : X) (j : Nat) : Measure X :=
  sampleFromKernel (candidate j)
    ((condOn (marginal candidate A hA roundCost hcost x fallback j)
      Ttc.FiniteContinuingRetry.runningStates).map current)

/-- Survival normalization identity. -/
theorem survival_mul_proposal_apply
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost)
    (x fallback : X) (j : Nat)
    (hs0 : survival candidate A hA roundCost hcost x fallback j ≠ 0)
    {B : Set X} (hB : MeasurableSet B) :
    survival candidate A hA roundCost hcost x fallback j *
        proposal candidate A hA roundCost hcost x fallback j B =
      ∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
        candidate j (current s) B
        ∂(marginal candidate A hA roundCost hcost x fallback j) := by
  let rho := marginal candidate A hA roundCost hcost x fallback j
  let sv := survival candidate A hA roundCost hcost x fallback j
  let I := ∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
    candidate j (current s) B ∂rho
  have hstop : sv ≠ ⊤ := by
    exact measure_ne_top rho Ttc.FiniteContinuingRetry.runningStates
  have hp : proposal candidate A hA roundCost hcost x fallback j B = sv⁻¹ * I := by
    unfold proposal sampleFromKernel
    rw [Measure.bind_apply hB (candidate j).aemeasurable,
      lintegral_map ((candidate j).measurable_coe hB) measurable_current,
      condOn_def, lintegral_smul_measure]
    rfl
  rw [hp]
  exact ENNReal.mul_inv_cancel_left hs0 hstop

/-- The accepted increment at retry `j` is its first-hit weight times the normalized
accepted proposal law. -/
theorem accepted_increment_eq_weight_mul_condOn
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost)
    (x fallback : X) (j : Nat)
    (hs0 : survival candidate A hA roundCost hcost x fallback j ≠ 0)
    (ha0 : proposal candidate A hA roundCost hcost x fallback j A ≠ 0)
    {T : Set X} (hT : MeasurableSet T) :
    (∫⁻ s in Ttc.FiniteContinuingRetry.runningStates,
        candidate j (current s) (A ∩ T)
        ∂(marginal candidate A hA roundCost hcost x fallback j)) =
      (survival candidate A hA roundCost hcost x fallback j *
          proposal candidate A hA roundCost hcost x fallback j A) *
        condOn (proposal candidate A hA roundCost hcost x fallback j) A T := by
  let p := proposal candidate A hA roundCost hcost x fallback j
  have hptop : p A ≠ ⊤ := by
    haveI : IsProbabilityMeasure p := by
      unfold p proposal sampleFromKernel
      have hsv0 : marginal candidate A hA roundCost hcost x fallback j
          Ttc.FiniteContinuingRetry.runningStates ≠ 0 := hs0
      letI : IsProbabilityMeasure
          (condOn (marginal candidate A hA roundCost hcost x fallback j)
            Ttc.FiniteContinuingRetry.runningStates) :=
        Arlib.isProbabilityMeasure_condOn _ hsv0 (measure_ne_top _ _)
      letI : IsProbabilityMeasure
          ((condOn (marginal candidate A hA roundCost hcost x fallback j)
            Ttc.FiniteContinuingRetry.runningStates).map current) :=
        Measure.isProbabilityMeasure_map measurable_current.aemeasurable
      exact sampleFromKernel.isProbabilityMeasure (candidate j) _
    exact measure_ne_top p A
  rw [← survival_mul_proposal_apply candidate A hA roundCost hcost x fallback j
    hs0 (hA.inter hT)]
  rw [condOn_apply p hA hT]
  change _ = (_ * p A) * (p (T ∩ A) / p A)
  rw [show T ∩ A = A ∩ T from inter_comm T A, div_eq_mul_inv]
  have hcancel : p A * (p A)⁻¹ = 1 := ENNReal.mul_inv_cancel ha0 hptop
  calc
    _ = (p A * (p A)⁻¹) *
        (survival candidate A hA roundCost hcost x fallback j * p (A ∩ T)) := by
      rw [hcancel, one_mul]
    _ = (survival candidate A hA roundCost hcost x fallback j * p A) *
        (p (A ∩ T) * (p A)⁻¹) := by ac_rfl

/-- Exact survival recurrence of the concrete finite state machine. -/
theorem survival_succ
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost)
    (x fallback : X) (j : Nat)
    (hs0 : survival candidate A hA roundCost hcost x fallback j ≠ 0) :
    survival candidate A hA roundCost hcost x fallback (j + 1) =
      survival candidate A hA roundCost hcost x fallback j *
        proposal candidate A hA roundCost hcost x fallback j Aᶜ := by
  unfold survival marginal
  rw [Arlib.adaptiveMarginal]
  rw [Measure.bind_apply Ttc.FiniteContinuingRetry.measurableSet_runningStates
    (schedule candidate A hA roundCost hcost j).aemeasurable]
  have hfun : (fun s : RetryState X X ↦
      schedule candidate A hA roundCost hcost j s
        Ttc.FiniteContinuingRetry.runningStates) =
      Ttc.FiniteContinuingRetry.runningStates.indicator
        (fun s ↦ candidate j (current s) Aᶜ) := by
    funext s
    rw [schedule, retryStep_runningStates]
    by_cases hs : accepted s = true
    · simp [hs, Ttc.FiniteContinuingRetry.runningStates, acceptedStates]
    · simp [hs, Ttc.FiniteContinuingRetry.runningStates, acceptedStates]
  rw [hfun]
  change (∫⁻ s,
      Ttc.FiniteContinuingRetry.runningStates.indicator
        (fun s ↦ candidate j (current s) Aᶜ) s
      ∂(Arlib.adaptiveMarginal (schedule candidate A hA roundCost hcost)
        (initialLaw x fallback) j)) =
    Arlib.adaptiveMarginal (schedule candidate A hA roundCost hcost)
        (initialLaw x fallback) j Ttc.FiniteContinuingRetry.runningStates *
      proposal candidate A hA roundCost hcost x fallback j Aᶜ
  rw [lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
  simpa only [survival, marginal] using
    (survival_mul_proposal_apply candidate A hA roundCost hcost x fallback j
      hs0 hA.compl).symm

/-- Accepted output mass telescopes into the actual first-hit weights. -/
theorem acceptedOutputEvent_eq_sum
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost)
    (x fallback : X) (L : Nat)
    (hs0 : ∀ j, j < L →
      survival candidate A hA roundCost hcost x fallback j ≠ 0)
    (ha0 : ∀ j, j < L →
      proposal candidate A hA roundCost hcost x fallback j A ≠ 0)
    {T : Set X} (hT : MeasurableSet T) :
    marginal candidate A hA roundCost hcost x fallback L (acceptedOutputEvent T) =
      ∑ j ∈ Finset.range L,
        (survival candidate A hA roundCost hcost x fallback j *
          proposal candidate A hA roundCost hcost x fallback j A) *
            condOn (proposal candidate A hA roundCost hcost x fallback j) A T := by
  let P := schedule candidate A hA roundCost hcost
  let mu0 := initialLaw x fallback
  let g : Nat → RetryState X X → ENNReal := fun j s ↦
    candidate j (current s) (A ∩ T)
  have hg : ∀ j, Measurable (g j) := fun j ↦
    ((candidate j).measurable_coe (hA.inter hT)).comp measurable_current
  have hstep : ∀ j s, P j s (acceptedOutputEvent T) =
      if s ∈ (acceptedStates : Set (RetryState X X)) then
        (acceptedOutputEvent T).indicator (fun _ ↦ (1 : ENNReal)) s else g j s := by
    intro j s
    dsimp only [P]
    have hh := retryStep_acceptedOutputEvent candidate A hA id measurable_id id
      measurable_id roundCost hcost j s hT
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
  exact accepted_increment_eq_weight_mul_condOn candidate A hA roundCost hcost
    x fallback j (hs0 j (Finset.mem_range.1 hj)) (ha0 j (Finset.mem_range.1 hj)) hT

/-- Concrete construction of the full finite retry decomposition consumed by the
significant-survival TV capstone. -/
noncomputable def concreteDecomposition
    (candidate : Nat → Kernel X X) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set X) (hA : MeasurableSet A)
    (roundCost : X → ENNReal) (hcost : Measurable roundCost)
    (x fallback : X) (L : Nat) (eta r : ENNReal)
    (hs0 : ∀ j,
      survival candidate A hA roundCost hcost x fallback j ≠ 0)
    (ha0 : ∀ j,
      proposal candidate A hA roundCost hcost x fallback j A ≠ 0)
    (hreject : ∀ j, eta ≤
      survival candidate A hA roundCost hcost x fallback j →
      proposal candidate A hA roundCost hcost x fallback j Aᶜ ≤ r) :
    Ttc.FiniteContinuingRetry.FiniteRetryDecomposition L
      (Measure.map (cutoffOutput (E := X) fallback)
        (marginal candidate A hA roundCost hcost x fallback L)) A fallback eta r := by
  let w : Fin L → ENNReal := fun i ↦
    survival candidate A hA roundCost hcost x fallback i *
      proposal candidate A hA roundCost hcost x fallback i A
  let q : Fin L → Measure X := fun i ↦
    proposal candidate A hA roundCost hcost x fallback i
  let s := survival candidate A hA roundCost hcost x fallback
  have hpall : ∀ j, IsProbabilityMeasure
      (proposal candidate A hA roundCost hcost x fallback j) := by
    intro j
    unfold proposal sampleFromKernel
    letI : IsProbabilityMeasure
        (condOn (marginal candidate A hA roundCost hcost x fallback j)
          Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ (hs0 j) (measure_ne_top _ _)
    letI : IsProbabilityMeasure
        ((condOn (marginal candidate A hA roundCost hcost x fallback j)
          Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    infer_instance
  letI : ∀ j, IsProbabilityMeasure
      (proposal candidate A hA roundCost hcost x fallback j) := hpall
  have hqprob : ∀ i, IsProbabilityMeasure (q i) := by
    intro i; dsimp only [q]; infer_instance
  letI : ∀ i, IsProbabilityMeasure (q i) := hqprob
  have hout : Measure.map (cutoffOutput (E := X) fallback)
      (marginal candidate A hA roundCost hcost x fallback L) =
      Ttc.ContinuingRejectionSignificant.acceptedMixture L w
        (fun i ↦ condOn (q i) A) (s L) fallback := by
    apply map_cutoffOutput_eq_acceptedMixture_of_apply
    intro T hT
    have hacc := acceptedOutputEvent_eq_sum candidate A hA roundCost hcost x fallback L
      (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j) hT
    rw [← Fin.sum_univ_eq_sum_range] at hacc
    simpa only [w, q, s] using hacc
  have hmass : (∑ i, w i) + s L = 1 := by
    letI : ∀ i, IsProbabilityMeasure (condOn (q i) A) := fun i ↦
      Arlib.isProbabilityMeasure_condOn _ (by simpa only [q] using ha0 i)
        (measure_ne_top _ _)
    have hpart := accepted_add_survival_eq_one
      (marginal candidate A hA roundCost hcost x fallback L)
    have hacc := acceptedOutputEvent_eq_sum candidate A hA roundCost hcost x fallback L
      (fun j _ ↦ hs0 j) (fun j _ ↦ ha0 j)
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set X))
    rw [hacc] at hpart
    rw [← Fin.sum_univ_eq_sum_range] at hpart
    simpa only [w, q, s, survival,
      Ttc.FiniteContinuingRetryDecomposition.runningStates,
      Ttc.FiniteContinuingRetry.runningStates, measure_univ, mul_one] using hpart
  refine
    { w := w
      proposal := q
      proposal_probability := hqprob
      s := s
      output_eq := hout
      mass := hmass
      survival_zero := ?_
      survival_mono := ?_
      survival_contract := ?_ }
  · exact prob_le_one
  · intro j
    dsimp only [s]
    rw [survival_succ candidate A hA roundCost hcost x fallback j (hs0 j)]
    calc
      _ ≤ survival candidate A hA roundCost hcost x fallback j * 1 :=
        mul_le_mul_left' prob_le_one _
      _ = _ := mul_one _
  · intro j heta
    dsimp only [s] at heta ⊢
    rw [survival_succ candidate A hA roundCost hcost x fallback j (hs0 j)]
    simpa only [mul_comm] using
      (mul_le_mul_left' (hreject j heta)
        (survival candidate A hA roundCost hcost x fallback j))

#print axioms survival_succ
#print axioms acceptedOutputEvent_eq_sum
#print axioms concreteDecomposition

end Ttc.FiniteContinuingRetryConcreteDecomposition
