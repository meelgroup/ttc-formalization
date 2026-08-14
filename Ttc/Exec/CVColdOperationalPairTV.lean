import Ttc.Exec.CVColdOperationalKernel
import Ttc.Exec.CVGaussianWarmFallbackZeroSafe
import Ttc.Exec.CVGaussianAdaptiveMixing
import Ttc.Exec.FiniteContinuingRetryProjectedZeroSafe
import Ttc.Exec.FiniteContinuingRetryRandomFallback
import Ttc.Exec.FiniteContinuingRetryGaussian
import Ttc.Exec.FiniteContinuingRetryGaussianAugmentedPhase
import Ttc.Exec.CVCorrectedFixedBlockCost

/-!
# Zero-safe pair TV for the operational cold Gaussian kernel

This file supplies the distributional companion of `CVColdOperationalKernel`.  The
finite-retry self-fallback output is decomposed into unnormalised first-hit increments
and its actual unresolved tail.  Hence no global nonzero-survival or nonzero-acceptance
assumption is required.
-/

set_option autoImplicit false

namespace Ttc.CVColdOperationalPairTV

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryEmbeddedSelective
open Ttc.FiniteContinuingRetryProjectedWarm
open Ttc.FiniteContinuingRetryProjectedZeroSafe
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVCombinedContinuingAccept Ttc.CVCombinedContinuingRetryPhaseTV
open Ttc.CVGaussianAcceptedWarm Ttc.CVContinuingRetryParameters
open Ttc.CVColdOperationalKernel
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVHybridSchedule
open scoped ENNReal Classical BigOperators

variable {X E C F : Type*} [MeasurableSpace X] [MeasurableSpace E]
  [MeasurableSpace C] [MeasurableSpace F]

/-- Output submeasure carried by executions unresolved after the finite retry count. -/
noncomputable def embeddedRunningOutput
    (mu : Measure (RetryState E F)) : Measure F :=
  Measure.map output (mu.restrict Ttc.FiniteContinuingRetry.runningStates)

/-- Every embedded retry output is the sum of its accepted first-hit law and its actual
unresolved self-fallback tail. -/
theorem map_output_eq_accepted_add_running
    (mu : Measure (RetryState E F)) :
    Measure.map output mu = acceptedOutputSubmeasure mu + embeddedRunningOutput mu := by
  ext T hT
  have hunion : (output : RetryState E F → F) ⁻¹' T =
      (acceptedStates ∩ output ⁻¹' T) ∪
        (Ttc.FiniteContinuingRetry.runningStates ∩ output ⁻¹' T) := by
    ext z
    by_cases hz : accepted z = true <;>
      simp [Ttc.FiniteContinuingRetry.runningStates, acceptedStates, hz]
  have hdisj : Disjoint (acceptedStates ∩ (output : RetryState E F → F) ⁻¹' T)
      (Ttc.FiniteContinuingRetry.runningStates ∩ output ⁻¹' T) :=
    Set.disjoint_left.2 fun _ ha hr ↦ hr.1 ha.1
  rw [Measure.map_apply measurable_output hT, hunion,
    measure_union hdisj
      (Ttc.FiniteContinuingRetry.measurableSet_runningStates.inter
        (hT.preimage measurable_output)), Measure.add_apply,
    acceptedOutputSubmeasure, Measure.map_apply measurable_output hT,
    Measure.restrict_apply (hT.preimage measurable_output),
    embeddedRunningOutput, Measure.map_apply measurable_output hT,
    Measure.restrict_apply (hT.preimage measurable_output)]
  rw [inter_comm acceptedStates, inter_comm Ttc.FiniteContinuingRetry.runningStates]

/-- Zero-safe selective comparison for an embedded retry retaining its actual unresolved
fallback.  This is the missing self-fallback analogue of
`tvLe_randomFallback_embeddedMarginal_selective_zeroSafe`. -/
theorem tvLe_map_output_embeddedMarginal_selective_zeroSafe
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
    TVLe (Measure.map output
      (embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L))
      target (acceptedError + (eta + r ^ L)) := by
  classical
  let inc : Fin L → Measure F := fun i ↦
    projectedFirstHitIncrement candidate A hA next hnext out hout roundCost hcost
      embed rho (id ∘ out) hout i
  let s : Nat → ENNReal := fun j ↦
    embeddedSurvival candidate A hA next hnext out hout roundCost hcost embed rho j
  let muL := embeddedMarginal candidate A hA next hnext out hout roundCost hcost embed rho L
  let tail : Measure F := embeddedRunningOutput muL
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
  have houtlaw : Measure.map output muL = (∑ i, inc i) + tail := by
    rw [map_output_eq_accepted_add_running, hacc]
  have hmass : (∑ i, inc i Set.univ) + tail Set.univ = 1 := by
    have h := congrArg (fun nu : Measure F ↦ nu Set.univ) houtlaw
    rw [Measure.map_apply measurable_output MeasurableSet.univ, preimage_univ,
      measure_univ] at h
    simpa only [Measure.add_apply, Measure.finsetSum_apply] using h.symm
  have hs0 : s 0 ≤ 1 := prob_le_one
  have hbadN := Ttc.ContinuingRejectionSelective.badWeights_add_survival_le_eta_add_pow
    (fun j ↦ if hj : j < L then inc ⟨j, hj⟩ Set.univ else 0) s L eta r
    (fun j hj ↦ by simpa [hj] using hrec j hj) hs0 hr hsmono (by
      intro j hj
      simpa only [s] using hcontract j hj)
  have htailMass : tail Set.univ = s L := by
    dsimp only [tail, s, muL, embeddedRunningOutput]
    rw [Measure.map_apply measurable_output MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
    rfl
  have hbad : (∑ i ∈ (Finset.univ : Finset (Fin L)).filter
      (fun i : Fin L ↦ ¬ eta ≤ s (i : Nat)), inc i Set.univ) + tail Set.univ ≤
      eta + r ^ L := by
    rw [Finset.sum_filter] at hbadN ⊢
    rw [← Fin.sum_univ_eq_sum_range] at hbadN
    simpa only [htailMass, Fin.is_lt, dif_pos] using hbadN
  rw [houtlaw]
  apply tvLe_sum_add_tail_selective_zeroSafe L inc tail target acceptedError
    (eta + r ^ L) (fun i ↦ eta ≤ s (i : Nat)) hmass hfinite
  · intro i hi
    simpa only [inc, s] using hgood0 i hi
  · intro i hi
    simpa only [inc, s] using hgood i hi
  · exact hbad

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Pair-valued zero-safe Gaussian selective theorem for the actual unresolved
self-fallback kernel. -/
theorem tvLe_gaussianAugmentedPhase_selective_zeroSafe
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    (deadline : ENNReal → Nat) (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho]
    (L : Nat) {pi tau : Measure (State n)} [IsProbabilityMeasure tau]
    {M eta zeta : ENNReal} (heta0 : eta ≠ 0)
    (hwarm : ∀ i : Nat, IsWarm M
      (Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent
        (augmentedMarginalOf K hK delta s c hdelta hc
          (fun _ ↦ deadline (M / eta)) rho i)) pi)
    (hmix : ∀ nu : Measure (State n),
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe
          (sampleFromKernel
            (iteratedKernel (lazy (speedyMetropolisGaussian K delta s))
              (deadline (M / eta))) nu) tau zeta)
    (heighth : ENNReal.ofReal (1 / 8 : Real) ≤
      SpeedyRejection.proposal tau (combinedAccept K c s))
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real)) :
    TVLe
      (Measure.map output
        (augmentedMarginalOf K hK delta s c hdelta hc
          (fun _ ↦ deadline (M / eta)) rho L))
      (scoreSeedReference c
        (Measure.map (combinedOutput c)
          (condOn (SpeedyRejection.proposal tau) (combinedAccept K c s))))
      (32 * zeta + (eta + continuingContraction ^ L)) := by
  have hideal0 : SpeedyRejection.proposal tau (combinedAccept K c s) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) heighth)
  let targetScore := Measure.map (combinedOutput c)
    (condOn (SpeedyRejection.proposal tau) (combinedAccept K c s))
  let target := scoreSeedReference c targetScore
  letI : IsProbabilityMeasure
      (condOn (SpeedyRejection.proposal tau) (combinedAccept K c s)) :=
    Arlib.isProbabilityMeasure_condOn _ hideal0 (measure_ne_top _ _)
  letI : IsProbabilityMeasure targetScore :=
    Measure.isProbabilityMeasure_map (measurable_combinedOutput c).aemeasurable
  letI : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map (by fun_prop :
      Measurable (fun y : State n ↦ (y, c • y))).aemeasurable
  let steps : Nat → Nat := fun _ ↦ deadline (M / eta)
  let cand := phaseCandidate K hK delta s hdelta steps
  let A := costedCombinedAccept K c s
  have hgoodPair (i : Fin L)
      (hi : eta ≤ augmentedSurvivalOf K hK delta s c hdelta hc steps rho i) :
      projectedFirstHitIncrement cand A (measurableSet_costedCombinedAccept hK hc)
          rejectedNext measurable_rejectedNext
          (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
          roundQueryCost measurable_roundQueryCost augmentedEmbedding rho
          (id ∘ augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c) i Set.univ ≠ 0 ∧
        TVLe (condOn
          (projectedFirstHitIncrement cand A (measurableSet_costedCombinedAccept hK hc)
            rejectedNext measurable_rejectedNext
            (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
            roundQueryCost measurable_roundQueryCost augmentedEmbedding rho
            (id ∘ augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c) i)
          Set.univ) target (32 * zeta) := by
    have hsurv : augmentedSurvivalOf K hK delta s c hdelta hc steps rho i ≠ 0 :=
      ne_of_gt ((pos_iff_ne_zero.2 heta0).trans_le hi)
    let rhoJ := augmentedMarginalOf K hK delta s c hdelta hc steps rho i
    haveI : IsProbabilityMeasure rhoJ :=
      isProbabilityMeasure_embeddedMarginal cand A
        (measurableSet_costedCombinedAccept hK hc)
        rejectedNext measurable_rejectedNext
        (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
        roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
        rho i
    letI : IsProbabilityMeasure (condOn rhoJ Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ (by
        simpa only [rhoJ, augmentedMarginalOf, augmentedSurvivalOf, embeddedSurvival]
          using hsurv) (measure_ne_top _ _)
    letI : IsProbabilityMeasure
        ((condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    let p := augmentedProposalOf K hK delta s c hdelta hc steps rho i
    haveI : IsProbabilityMeasure p := by
      change IsProbabilityMeasure
        (sampleFromKernel (cand i)
          ((condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current))
      infer_instance
    letI : IsProbabilityMeasure (Measure.map Prod.snd p) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    have hcand := Ttc.CVGaussianKilledRetryWarm.tvLe_augmentedProposalOf_at_significant_killed
      hK hdelta hc deadline rho i heta0 (hwarm i)
      (by simpa only [steps] using hi) hmix
    have hacc16 := sixteenth_le_acceptance_of_tvLe_eighth hcand
      (measurableSet_combinedAccept hK hc) heighth hzeta
    have hpA0 : p A ≠ 0 := by
      have hmap : (Measure.map Prod.snd p) (combinedAccept K c s) = p A := by
        rw [Measure.map_apply measurable_snd (measurableSet_combinedAccept hK hc)]
        rfl
      rw [hmap] at hacc16
      exact ne_of_gt ((ENNReal.ofReal_pos.2 (by norm_num)).trans_le hacc16)
    have hinc0 : projectedFirstHitIncrement cand A
          (measurableSet_costedCombinedAccept hK hc)
          rejectedNext measurable_rejectedNext
          (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
          roundQueryCost measurable_roundQueryCost augmentedEmbedding rho
          (id ∘ augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c) i
          Set.univ ≠ 0 := by
      rw [projectedFirstHit_univ_eq_survival_mul_proposal cand A
        (measurableSet_costedCombinedAccept hK hc)
        rejectedNext measurable_rejectedNext
        (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
        roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
        rho (id ∘ augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c) i (by
          simpa only [steps, augmentedSurvivalOf] using hsurv)]
      exact mul_ne_zero hsurv hpA0
    refine ⟨hinc0, ?_⟩
    rw [condOn_projectedFirstHit_eq_map_condOn_embeddedProposal cand A
      (measurableSet_costedCombinedAccept hK hc)
      rejectedNext measurable_rejectedNext
      (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
      roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
      rho (id ∘ augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c) i (by
        simpa only [steps, augmentedSurvivalOf] using hsurv) (by
        simpa only [p, A, steps, augmentedProposalOf] using hpA0)]
    have hscore : TVLe
        (Measure.map (acceptedOutput c) (condOn p A)) targetScore (32 * zeta) := by
      rw [show A = costedCombinedAccept K c s from rfl,
        map_acceptedOutput_condOn_costedCombinedAccept
          (nu := p) (K := K) (c := c) (s := s) hK hc]
      exact (Ttc.ContinuingRejectionSignificant.tvLe_condOn_eighth
        (Measure.map Prod.snd p) (SpeedyRejection.proposal tau)
        (measurableSet_combinedAccept hK hc) hcand heighth hzeta).map
          (measurable_combinedOutput c)
    simpa only [Function.id_comp, target, targetScore, scoreSeedReference, p,
      augmentedProposalOf, cand, A, steps] using
      (tvLe_map_augmentedAcceptedOutput_of_score c hc hscore)
  apply tvLe_map_output_embeddedMarginal_selective_zeroSafe cand A
    (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
    (by intro a; simp [augmentedEmbedding, accepted]) rho L target eta
    continuingContraction (32 * zeta)
  · intro i hi
    exact (hgoodPair i (by simpa only [steps, cand, A, augmentedSurvivalOf] using hi)).1
  · intro i hi
    exact (hgoodPair i (by simpa only [steps, cand, A, augmentedSurvivalOf] using hi)).2
  · rw [continuingContraction]
    norm_num
  · intro j hj
    have hsurv : augmentedSurvivalOf K hK delta s c hdelta hc steps rho j ≠ 0 :=
      ne_of_gt ((pos_iff_ne_zero.2 heta0).trans_le (by
        simpa only [steps, cand, A, augmentedSurvivalOf] using hj))
    let rhoJ := augmentedMarginalOf K hK delta s c hdelta hc steps rho j
    haveI : IsProbabilityMeasure rhoJ :=
      isProbabilityMeasure_embeddedMarginal cand A
        (measurableSet_costedCombinedAccept hK hc)
        rejectedNext measurable_rejectedNext
        (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
        roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
        rho j
    letI : IsProbabilityMeasure (condOn rhoJ Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ (by
        simpa only [rhoJ, augmentedMarginalOf, augmentedSurvivalOf, embeddedSurvival]
          using hsurv) (measure_ne_top _ _)
    letI : IsProbabilityMeasure
        ((condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    let p := augmentedProposalOf K hK delta s c hdelta hc steps rho j
    haveI : IsProbabilityMeasure p := by
      change IsProbabilityMeasure
        (sampleFromKernel (cand j)
          ((condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current))
      infer_instance
    letI : IsProbabilityMeasure (Measure.map Prod.snd p) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    have hcand := Ttc.CVGaussianKilledRetryWarm.tvLe_augmentedProposalOf_at_significant_killed
      hK hdelta hc deadline rho j heta0 (hwarm j) (by
        simpa only [steps, cand, A, augmentedSurvivalOf] using hj) hmix
    have hrej := rejection_le_continuingContraction_of_tvLe
      (Measure.map Prod.snd p) (SpeedyRejection.proposal tau)
      (measurableSet_combinedAccept hK hc) hcand heighth hzeta
    rw [embeddedSurvival_succ cand A (measurableSet_costedCombinedAccept hK hc)
      rejectedNext measurable_rejectedNext
      (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
      roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
      rho j (by simpa only [steps, augmentedSurvivalOf] using hsurv)]
    have hpcompl : p Aᶜ ≤ continuingContraction := by
      have hmap : (Measure.map Prod.snd p) (combinedAccept K c s)ᶜ = p Aᶜ := by
        rw [Measure.map_apply measurable_snd (measurableSet_combinedAccept hK hc).compl]
        rfl
      simpa only [hmap] using hrej
    simpa only [p, augmentedProposalOf, cand, A, steps, mul_comm] using
      mul_le_mul_left' hpcompl
        (embeddedSurvival cand A (measurableSet_costedCombinedAccept hK hc)
          rejectedNext measurable_rejectedNext
          (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
          roundQueryCost measurable_roundQueryCost augmentedEmbedding rho j)

/-- Concrete radius-four pair TV.  The speedy mixing deadline, killed-current warmth,
stationary probability measure, and ideal joint-acceptance lower bound are all discharged
from cold-body geometry. -/
theorem tvLe_coldGaussianKernel_adjustable_zeroSafe
    (hn : 21 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0) (i : Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)))
    (L : Nat) :
    let delta := fixedRadiusFourDelta n (fixedSigmaSq n s0 i)
    let s := fixedSigmaSq n s0 i
    let c := 1 - 1 / (2 * (n : Real))
    let deadline := fun W : ENNReal ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n delta s W zeta
    let retrySteps : Nat → Nat → Nat := fun _ _ ↦ deadline (M / eta)
    let retries : Nat → Nat := fun _ ↦ L
    TVLe
      (sampleFromKernel
        (coldGaussianKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i) rho)
      (scoreSeedReference c
        (Measure.map (combinedOutput c)
          (condOn
            (SpeedyRejection.proposal
              (ellGaussianProb (fixedRadiusFourBody K s) delta s))
            (combinedAccept (fixedRadiusFourBody K s) c s))))
      (32 * zeta + (eta + continuingContraction ^ L)) := by
  dsimp only
  let s := fixedSigmaSq n s0 i
  let delta := fixedRadiusFourDelta n s
  let body := fixedRadiusFourBody K s
  let c : Real := 1 - 1 / (2 * (n : Real))
  let pi := ellGaussianProb body delta s
  let deadline := fun W : ENNReal ↦
    Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n delta s W zeta
  let retrySteps : Nat → Nat → Nat := fun _ _ ↦ deadline (M / eta)
  let retries : Nat → Nat := fun _ ↦ L
  have hn1 : 1 ≤ n := by omega
  have hs : 0 < s := by
    dsimp only [s]
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) i
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact fixedRadiusFourDelta_pos hn1 hs
  have hbodyM : MeasurableSet body := by
    exact measurableSet_fixedRadiusFourBody hK _
  have hbodyC : Convex Real body := convex_fixedRadiusFourBody hKc _
  have hbodyBall : ball (0 : State n) 1 ⊆ body := by
    exact Arlib.MarkovChains.unitBall_subset_inter_closedBall hball hrad
  have hbody0 : volume body ≠ 0 := by
    exact Arlib.MarkovChains.volume_inter_closedBall_ne_zero hball hrad
  have hbodyTop : volume body ≠ ⊤ := by
    exact Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
  have hc0 : 0 < c := by
    dsimp only [c]
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn1
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp only [c]
    have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hcne : c ≠ 0 := hc0.ne'
  have hdeltan : delta ≤ 1 / (2 * (n : Real)) := by
    exact fixedRadiusFourDelta_le_n
  have hdeltaC : delta ≤ 1 - c := by
    dsimp only [c]
    linarith
  have hM0 : ellGaussianMeasure body delta s Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hbodyM hbodyC hbodyBall
      hc0 hc1 hdelta hdeltaC hs
  have hMfinite : ellGaussianMeasure body delta s Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hs body delta hbodyTop
  letI : IsProbabilityMeasure pi := by
    dsimp only [pi]
    exact isProbabilityMeasure_ellGaussianProb hM0 hMfinite
  let rhoPair := Measure.map (seedEmbedding c) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  have hkilled : ∀ j, IsWarm M
      (Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent
        (augmentedMarginalOf body hbodyM delta s c hdelta hcne
          (fun _ ↦ deadline (M / eta)) rhoPair j)) pi := by
    intro j
    exact Ttc.CVGaussianWarmFallbackAnalytic.isWarm_runningCurrent_augmentedMarginalOf_gaussian
      hbodyM hdelta hcne rho (by simpa only [pi, body, delta, s] using hwarm)
      (fun _ ↦ deadline (M / eta)) j
  have hMetaTop : M / eta ≠ ⊤ := ENNReal.div_ne_top hMtop heta0
  have hMeta1 : 1 ≤ M / eta := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl heta0) (Or.inl hetatop)).2
    rw [one_mul]
    exact heta1.trans hM1
  have hmix : ∀ nu : Measure (State n),
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe
          (sampleFromKernel
            (iteratedKernel (lazy (speedyMetropolisGaussian body delta s))
              (deadline (M / eta))) nu) pi zeta := by
    intro nu hnu hprob
    letI : IsProbabilityMeasure nu := hprob
    apply Ttc.CVGaussianAdaptiveMixing.tvLe_adjustableSpeedyDeadline
      (q := 4) (R := 4 * Real.sqrt s * Real.sqrt n)
      hn (by norm_num) hs hdelta
      (by
        simpa only [body, delta, s,
          max_eq_left (by norm_num : (8 : Real) ≥ 2 * 4)] using
          (fixedRadiusFourDelta_le_radius (n := n) (s := s)))
      hbodyM hbodyC hbody0 (by positivity)
      (fun x hx ↦ norm_le_fixedRadiusFour hx) le_rfl
      hMeta1 hMetaTop hzeta0 hzetatop (hzeta16.trans (by norm_num))
      (by simpa only [pi] using hnu)
  have heighth : ENNReal.ofReal (1 / 8 : Real) ≤
      SpeedyRejection.proposal pi (combinedAccept body c s) := by
    simpa only [pi, body, delta, s, c] using
      (Ttc.CVIdealCombinedAccepted.eighth_le_ellGaussianProb_combinedAccept
        hn1 hbodyM hbodyC hbodyBall hbodyTop hdelta hdeltan hs)
  have hpair := tvLe_gaussianAugmentedPhase_selective_zeroSafe
    hbodyM hdelta hcne deadline rhoPair L (pi := pi) (tau := pi)
    heta0 hkilled hmix heighth hzeta16
  rw [sampleFrom_coldGaussianKernel hn1 K hK s0 hs0 retrySteps retries rho i]
  simpa only [body, delta, s, c, pi, deadline, retrySteps, retries] using hpair

/-- Concrete `hphaseSeedTV` for the operational cold phase.  Its target is the
standard-shrink image of the ideal accepted score law.  In particular, this theorem
removes the pair-TV premise from the heterogeneous retained-history certificate. -/
theorem tvLe_seed_bind_coldGaussianCostedKernel_adjustable_zeroSafe
    (hn : 21 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0) (i : Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)))
    (L : Nat) :
    let delta := fixedRadiusFourDelta n (fixedSigmaSq n s0 i)
    let s := fixedSigmaSq n s0 i
    let c := 1 - 1 / (2 * (n : Real))
    let deadline := fun W : ENNReal ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n delta s W zeta
    let retrySteps : Nat → Nat → Nat := fun _ _ ↦ deadline (M / eta)
    let retries : Nat → Nat := fun _ ↦ L
    TVLe
      (rho.bind (Kernel.map
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
      (Measure.map (fun y : State n ↦ c • y)
        (Measure.map (combinedOutput c)
          (condOn
            (SpeedyRejection.proposal
              (ellGaussianProb (fixedRadiusFourBody K s) delta s))
            (combinedAccept (fixedRadiusFourBody K s) c s))))
      (32 * zeta + (eta + continuingContraction ^ L)) := by
  dsimp only
  let s := fixedSigmaSq n s0 i
  let delta := fixedRadiusFourDelta n s
  let c : Real := 1 - 1 / (2 * (n : Real))
  let deadline := fun W : ENNReal ↦
    Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n delta s W zeta
  let retrySteps : Nat → Nat → Nat := fun _ _ ↦ deadline (M / eta)
  let retries : Nat → Nat := fun _ ↦ L
  apply tvLe_seed_bind_coldGaussianCostedKernel_of_pair
    (by omega : 1 ≤ n) K hK s0 hs0 retrySteps retries rho i
  simpa only [s, delta, c, deadline, retrySteps, retries] using
    (tvLe_coldGaussianKernel_adjustable_zeroSafe
      hn K hK hKc hball s0 hs0 i rho hM1 hMtop heta0 hetatop heta1
      hzeta0 hzetatop hzeta16 hrad hwarm L)

/-- Global-schedule form of the concrete cold `hphaseSeedTV`.  Only the retry policy at
the current phase index is relevant, so a genuinely phase-dependent operational schedule
may be supplied through the two pointwise identifications. -/
theorem tvLe_seed_bind_coldGaussianCostedKernel_adjustable_zeroSafe_of_eq
    (hn : 21 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)))
    (L : Nat)
    (hsteps : retrySteps i = fun _ ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i) (M / eta) zeta)
    (hretries : retries i = L) :
    let delta := fixedRadiusFourDelta n (fixedSigmaSq n s0 i)
    let s := fixedSigmaSq n s0 i
    let c := 1 - 1 / (2 * (n : Real))
    TVLe
      (rho.bind (Kernel.map
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
      (Measure.map (fun y : State n ↦ c • y)
        (Measure.map (combinedOutput c)
          (condOn
            (SpeedyRejection.proposal
              (ellGaussianProb (fixedRadiusFourBody K s) delta s))
            (combinedAccept (fixedRadiusFourBody K s) c s))))
      (32 * zeta + (eta + continuingContraction ^ L)) := by
  dsimp only
  let delta := fixedRadiusFourDelta n (fixedSigmaSq n s0 i)
  let s := fixedSigmaSq n s0 i
  let c : Real := 1 - 1 / (2 * (n : Real))
  let localSteps : Nat → Nat → Nat := fun _ _ ↦
    Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n delta s (M / eta) zeta
  let localRetries : Nat → Nat := fun _ ↦ L
  have hlocal := tvLe_seed_bind_coldGaussianCostedKernel_adjustable_zeroSafe
    hn K hK hKc hball s0 hs0 i rho hM1 hMtop heta0 hetatop heta1
      hzeta0 hzetatop hzeta16 hrad hwarm L
  have hkernel :
      coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i =
        coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          localSteps localRetries i := by
    unfold coldGaussianCostedKernel
    rw [hsteps, hretries]
  rw [hkernel]
  simpa only [delta, s, c, localSteps, localRetries] using hlocal

#print axioms tvLe_coldGaussianKernel_adjustable_zeroSafe
#print axioms tvLe_seed_bind_coldGaussianCostedKernel_adjustable_zeroSafe
#print axioms tvLe_seed_bind_coldGaussianCostedKernel_adjustable_zeroSafe_of_eq

#print axioms map_output_eq_accepted_add_running
#print axioms tvLe_map_output_embeddedMarginal_selective_zeroSafe
#print axioms tvLe_gaussianAugmentedPhase_selective_zeroSafe

end Ttc.CVColdOperationalPairTV
