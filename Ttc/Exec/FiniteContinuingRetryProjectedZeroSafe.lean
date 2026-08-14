import Ttc.Exec.FiniteContinuingRetryProjectedWarm
import Ttc.Exec.FiniteContinuingRetrySelfSelective

/-!
# Zero-safe selective first-hit decomposition

The normalized retry APIs are unusable after the survival mass becomes zero.  This file
keeps every first-hit contribution unnormalised, normalizes only the significant ones,
and charges the remaining contributions together with the unresolved tail.
-/

namespace Ttc.FiniteContinuingRetryProjectedZeroSafe

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryEmbeddedSelective
open Ttc.FiniteContinuingRetryProjectedWarm
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.FiniteContinuingRetrySelfSelective
open Ttc.CVSequentialPhaseSampler
open scoped ENNReal Classical BigOperators

variable {F : Type*} [MeasurableSpace F]

/-- A finite nonzero measure is its mass times its normalization on `univ`. -/
theorem mass_smul_condOn_univ (mu : Measure F) (h0 : mu Set.univ ≠ 0)
    (htop : mu Set.univ ≠ ⊤) :
    mu Set.univ • condOn mu Set.univ = mu := by
  rw [condOn_def, Measure.restrict_univ, smul_smul,
    ENNReal.mul_inv_cancel h0 htop, one_smul]

/-- Zero-safe selective mixture comparison.  Only good components are normalized;
all bad components and `tail` remain one unnormalised error submeasure. -/
theorem tvLe_sum_add_tail_selective_zeroSafe
    (L : Nat) (inc : Fin L → Measure F) (tail target : Measure F)
    [IsProbabilityMeasure target]
    (delta eta : ENNReal) (Good : Fin L → Prop) [DecidablePred Good]
    (hmass : (∑ i, inc i Set.univ) + tail Set.univ = 1)
    (hfinite : ∀ i, inc i Set.univ ≠ ⊤)
    (hgood0 : ∀ i, Good i → inc i Set.univ ≠ 0)
    (hgood : ∀ i, Good i → TVLe (condOn (inc i) Set.univ) target delta)
    (hbad : (∑ i with ¬ Good i, inc i Set.univ) + tail Set.univ ≤ eta) :
    TVLe ((∑ i, inc i) + tail) target (delta + eta) := by
  classical
  let q : Fin L → Measure F := fun i ↦
    if h0 : inc i Set.univ = 0 then target else condOn (inc i) Set.univ
  have hqprob : ∀ i, IsProbabilityMeasure (q i) := by
    intro i
    dsimp only [q]
    split_ifs with h0
    · infer_instance
    · exact Arlib.isProbabilityMeasure_condOn _ h0 (hfinite i)
  letI : ∀ i, IsProbabilityMeasure (q i) := hqprob
  have hrewrite : ∀ i, inc i Set.univ • q i = inc i := by
    intro i
    dsimp only [q]
    split_ifs with h0
    · have hmu : inc i = 0 := by
        ext S hS
        have hS0 : inc i S = 0 := measure_mono_null (subset_univ S) h0
        simpa using hS0
      simp [h0, hmu]
    · exact mass_smul_condOn_univ (inc i) h0 (hfinite i)
  have hsum : (∑ i, inc i Set.univ • q i) = ∑ i, inc i := by
    apply Finset.sum_congr rfl
    intro i _
    exact hrewrite i
  rw [← hsum]
  apply tvLe_sum_smul_add_tail_selective L (fun i ↦ inc i Set.univ) q tail target
    delta eta Good
  · exact hmass
  · intro i hi
    simp only [q, dif_neg (hgood0 i hi)]
    exact hgood i hi
  · exact hbad

variable {X E C : Type*} [MeasurableSpace X] [MeasurableSpace E]
  [MeasurableSpace C]

/-- The projected first-hit mass plus the next survival mass is the current survival
mass. This killed-transition identity is valid even when the current mass is zero. -/
theorem projectedFirstHit_univ_add_embeddedSurvival_succ
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (rho : Measure X) [IsProbabilityMeasure rho]
    (seed : C → F) (hseed : Measurable seed) (j : Nat) :
    projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
          embed rho seed hseed j Set.univ +
        embeddedSurvival candidate A hA next hnext out hout roundCost hcost
          embed rho (j + 1) =
      embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j := by
  let mu := embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j
  let cur := runningCurrent mu
  have hinc : projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
        embed rho seed hseed j Set.univ = ∫⁻ x, candidate j x A ∂cur := by
    rw [projectedFirstHitIncrement, sampleFromKernel,
      Measure.bind_apply MeasurableSet.univ
        (acceptedProjectedKernel candidate A hA seed hseed j).aemeasurable]
    apply lintegral_congr
    intro x
    rw [acceptedProjectedKernel, Kernel.map_apply _ hseed,
      Measure.map_apply hseed MeasurableSet.univ, preimage_univ,
      Kernel.restrict_apply' (candidate j) hA _ MeasurableSet.univ, univ_inter]
  have hnextSurv : embeddedSurvival candidate A hA next hnext out hout roundCost hcost
        embed rho (j + 1) = ∫⁻ x, candidate j x Aᶜ ∂cur := by
    have hsurv : embeddedSurvival candidate A hA next hnext out hout roundCost hcost
        embed rho (j + 1) = Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent
          (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho
            (j + 1)) Set.univ := by
      rw [runningCurrent, Measure.map_apply measurable_current MeasurableSet.univ,
        preimage_univ, Measure.restrict_apply_univ]
      simp [embeddedSurvival]
    rw [hsurv]
    rw [runningCurrent_embeddedMarginal_succ candidate A hA next hnext out hout
      roundCost hcost embed hembed rho j]
    rw [Measure.bind_apply MeasurableSet.univ
      (Ttc.FiniteContinuingRetrySelfCurrentWarm.rejectedKernel
        candidate A hA next hnext j).aemeasurable]
    apply lintegral_congr
    intro x
    rw [Ttc.FiniteContinuingRetrySelfCurrentWarm.rejectedKernel,
      Kernel.map_apply _ hnext,
      Measure.map_apply hnext MeasurableSet.univ, preimage_univ,
      Kernel.restrict_apply' (candidate j) hA.compl _ MeasurableSet.univ, univ_inter]
  rw [hinc, hnextSurv, ← lintegral_add_left]
  · have hfun : (fun x ↦ candidate j x A + candidate j x Aᶜ) = fun _ ↦ 1 := by
      funext x
      exact prob_add_prob_compl hA
    rw [hfun, lintegral_one]
    change cur Set.univ = _
    dsimp only [cur, mu]
    rw [Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent,
      Measure.map_apply measurable_current MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ]
    simp [embeddedSurvival, mu]
  · exact (candidate j).measurable_coe hA

/-- On a positive-survival, positive-acceptance retry, normalizing the killed first-hit
contribution is exactly conditioning the normalized candidate proposal. -/
theorem condOn_projectedFirstHit_eq_map_condOn_embeddedProposal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (rho : Measure X) [IsProbabilityMeasure rho]
    (seed : C → F) (hseed : Measurable seed) (j : Nat)
    (hs0 : embeddedSurvival candidate A hA next hnext out hout roundCost hcost
      embed rho j ≠ 0)
    (ha0 : embeddedProposal candidate A hA next hnext out hout roundCost hcost
      embed rho j A ≠ 0) :
    condOn
        (projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
          embed rho seed hseed j) Set.univ =
      Measure.map seed (condOn
        (embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho j) A) := by
  let p := embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho j
  let sv := embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j
  let inc := projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
    embed rho seed hseed j
  have hinc (T : Set F) (hT : MeasurableSet T) :
      inc T = sv * p (A ∩ seed ⁻¹' T) := by
    dsimp only [inc]
    rw [projectedFirstHitIncrement, sampleFromKernel,
      Measure.bind_apply hT (acceptedProjectedKernel candidate A hA seed hseed j).aemeasurable,
      runningCurrent,
      lintegral_map ((acceptedProjectedKernel candidate A hA seed hseed j).measurable_coe hT)
        measurable_current,
      ← lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
    simp_rw [acceptedProjectedKernel, Kernel.map_apply _ hseed,
      Measure.map_apply hseed hT,
      Kernel.restrict_apply' (candidate j) hA _ (hT.preimage hseed), inter_comm]
    rw [lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
    rw [embeddedSurvival_mul_proposal_apply candidate A hA next hnext out hout roundCost
      hcost embed hembed rho j hs0 (hA.inter (hT.preimage hseed))]
  have hincUniv : inc Set.univ = sv * p A := by
    rw [hinc Set.univ MeasurableSet.univ, preimage_univ, inter_univ]
  letI : IsProbabilityMeasure
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j) :=
    isProbabilityMeasure_embeddedMarginal candidate A hA next hnext out hout roundCost hcost
      embed hembed rho j
  have hsvTop : sv ≠ ⊤ := measure_ne_top _ _
  have hpTop : p A ≠ ⊤ := by
    haveI : IsProbabilityMeasure p := by
      unfold p embeddedProposal sampleFromKernel
      letI : IsProbabilityMeasure (condOn
          (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)
          Ttc.FiniteContinuingRetry.runningStates) :=
        Arlib.isProbabilityMeasure_condOn _ hs0 (measure_ne_top _ _)
      letI : IsProbabilityMeasure ((condOn
          (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j)
          Ttc.FiniteContinuingRetry.runningStates).map current) :=
        Measure.isProbabilityMeasure_map measurable_current.aemeasurable
      infer_instance
    exact measure_ne_top p A
  ext T hT
  rw [condOn_apply inc MeasurableSet.univ hT, inter_univ,
    Measure.map_apply hseed hT, condOn_apply p hA (hT.preimage hseed), hinc T hT,
    hincUniv]
  rw [show A ∩ seed ⁻¹' T = seed ⁻¹' T ∩ A from inter_comm _ _,
    ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl hs0) (Or.inl hsvTop),
    mul_assoc]
  calc
    sv⁻¹ * ((p A)⁻¹ * (sv * p (seed ⁻¹' T ∩ A))) =
        (sv⁻¹ * sv) * ((p A)⁻¹ * p (seed ⁻¹' T ∩ A)) := by ac_rfl
    _ = (p A)⁻¹ * p (seed ⁻¹' T ∩ A) := by
      rw [ENNReal.inv_mul_cancel hs0 hsvTop, one_mul]

theorem projectedFirstHit_univ_eq_survival_mul_proposal
    (candidate : Nat → Kernel E C) [∀ j, IsMarkovKernel (candidate j)]
    (A : Set C) (hA : MeasurableSet A)
    (next : C → E) (hnext : Measurable next)
    (out : C → F) (hout : Measurable out)
    (roundCost : C → ENNReal) (hcost : Measurable roundCost)
    (embed : X → RetryState E F) (hembed : Measurable embed)
    (rho : Measure X) [IsProbabilityMeasure rho]
    (seed : C → F) (hseed : Measurable seed) (j : Nat)
    (hs0 : embeddedSurvival candidate A hA next hnext out hout roundCost hcost
      embed rho j ≠ 0) :
    projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
        embed rho seed hseed j Set.univ =
      embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j *
        embeddedProposal candidate A hA next hnext out hout roundCost hcost embed rho j A := by
  rw [projectedFirstHitIncrement, sampleFromKernel,
    Measure.bind_apply MeasurableSet.univ
      (acceptedProjectedKernel candidate A hA seed hseed j).aemeasurable,
    runningCurrent,
    lintegral_map
      ((acceptedProjectedKernel candidate A hA seed hseed j).measurable_coe MeasurableSet.univ)
      measurable_current,
    ← lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
  simp_rw [acceptedProjectedKernel, Kernel.map_apply _ hseed,
    Measure.map_apply hseed MeasurableSet.univ, preimage_univ,
    Kernel.restrict_apply' (candidate j) hA _ MeasurableSet.univ, univ_inter]
  rw [lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates]
  exact embeddedSurvival_mul_proposal_apply candidate A hA next hnext out hout roundCost
    hcost embed hembed rho j hs0 hA |>.symm

/-- Retry-specific zero-safe selective comparison.  No survival/proposal nonzero
hypothesis is required outside significant indices. -/
theorem tvLe_randomFallback_embeddedMarginal_selective_zeroSafe
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
    (hgood0 : ∀ i : Fin L,
      eta ≤ embeddedSurvival candidate A hA next hnext out hout roundCost hcost
          embed rho i →
        projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
          embed rho (id ∘ out) hout i Set.univ ≠ 0)
    (hgood : ∀ i : Fin L,
      eta ≤ embeddedSurvival candidate A hA next hnext out hout roundCost hcost
          embed rho i →
        TVLe (condOn
          (projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
            embed rho (id ∘ out) hout i) Set.univ) target acceptedError)
    (hr : r ≤ 1)
    (hcontract : ∀ j,
      eta ≤ embeddedSurvival candidate A hA next hnext out hout roundCost hcost
          embed rho j →
        embeddedSurvival candidate A hA next hnext out hout roundCost hcost
          embed rho (j + 1) ≤
        r * embeddedSurvival candidate A hA next hnext out hout roundCost hcost
          embed rho j) :
    TVLe (sampleFromKernel (randomFallbackKernel fallback)
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L))
      target (acceptedError + (eta + r ^ L)) := by
  classical
  let inc : Fin L → Measure F := fun i ↦
    projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
      embed rho (id ∘ out) hout i
  let s : Nat → ENNReal := fun j ↦
    embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j
  let muL := embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L
  let tail : Measure F := s L • fallback
  letI : ∀ j, IsProbabilityMeasure
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho j) :=
    fun j ↦ isProbabilityMeasure_embeddedMarginal candidate A hA next hnext out hout
      roundCost hcost embed hembed rho j
  have hrec (j : Nat) (hj : j < L) :
      inc ⟨j, hj⟩ Set.univ + s (j + 1) = s j := by
    dsimp only [inc, s]
    exact projectedFirstHit_univ_add_embeddedSurvival_succ candidate A hA next hnext
      out hout roundCost hcost embed hembed rho (id ∘ out) hout j
  have hfinite : ∀ i, inc i Set.univ ≠ ⊤ := by
    intro i
    apply ne_of_lt
    calc
      inc i Set.univ ≤ inc i Set.univ + s ((i : Nat) + 1) := le_add_right le_rfl
      _ = s i := hrec i i.isLt
      _ ≤ 1 := prob_le_one
      _ < ⊤ := ENNReal.one_lt_top
  have hsmono : ∀ j, s (j + 1) ≤ s j := by
    intro j
    have hj := projectedFirstHit_univ_add_embeddedSurvival_succ candidate A hA next hnext
      out hout roundCost hcost embed hembed rho (id ∘ out) hout j
    dsimp only [s]
    rw [← hj]
    exact le_add_left le_rfl
  have hacc : acceptedOutputSubmeasure muL = ∑ i, inc i := by
    have h := map_seed_acceptedOutputSubmeasure_eq_sum_projectedFirstHit
      candidate A hA next hnext out hout roundCost hcost embed hembed hRunning rho
      id measurable_id L
    simpa only [Measure.map_id, Function.id_comp, inc, muL] using h
  haveI : IsProbabilityMeasure muL :=
    isProbabilityMeasure_embeddedMarginal candidate A hA next hnext out hout roundCost hcost
      embed hembed rho L
  have houtlaw : sampleFromKernel (randomFallbackKernel fallback) muL =
      (∑ i, inc i) + tail := by
    rw [sampleFrom_randomFallbackKernel muL fallback, hacc]
    rfl
  have hmass : (∑ i, inc i Set.univ) + tail Set.univ = 1 := by
    haveI : IsProbabilityMeasure
        (sampleFromKernel (randomFallbackKernel fallback) muL) := inferInstance
    have h := congrArg (fun nu : Measure F ↦ nu Set.univ) houtlaw
    simpa only [measure_univ, Measure.add_apply, Measure.finsetSum_apply] using h.symm
  have hs0 : s 0 ≤ 1 := prob_le_one
  have hbadN := Ttc.ContinuingRejectionSelective.badWeights_add_survival_le_eta_add_pow
    (fun j ↦ if hj : j < L then inc ⟨j, hj⟩ Set.univ else 0) s L eta r
    (fun j hj ↦ by simpa [hj] using hrec j hj) hs0 hr hsmono (by
      intro j hj
      simpa only [s] using hcontract j hj)
  have hbad : (∑ i ∈ (Finset.univ : Finset (Fin L)).filter
      (fun i : Fin L ↦ ¬ eta ≤ s (i : Nat)), inc i Set.univ) + tail Set.univ ≤
      eta + r ^ L := by
    rw [Finset.sum_filter] at hbadN ⊢
    rw [← Fin.sum_univ_eq_sum_range] at hbadN
    simpa only [tail, Measure.smul_apply, measure_univ, mul_one, smul_eq_mul,
      Fin.is_lt, dif_pos] using hbadN
  rw [houtlaw]
  apply tvLe_sum_add_tail_selective_zeroSafe L inc tail target acceptedError
    (eta + r ^ L) (fun i ↦ eta ≤ s (i : Nat)) hmass hfinite
  · intro i hi
    simpa only [inc, s] using hgood0 i hi
  · intro i hi
    simpa only [inc, s] using hgood i hi
  · exact hbad

#print axioms mass_smul_condOn_univ
#print axioms tvLe_sum_add_tail_selective_zeroSafe
#print axioms projectedFirstHit_univ_add_embeddedSurvival_succ
#print axioms condOn_projectedFirstHit_eq_map_condOn_embeddedProposal
#print axioms projectedFirstHit_univ_eq_survival_mul_proposal
#print axioms tvLe_randomFallback_embeddedMarginal_selective_zeroSafe

end Ttc.FiniteContinuingRetryProjectedZeroSafe
