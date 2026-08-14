import Ttc.Exec.CVGaussianWarmFallbackAnalytic
import Ttc.Exec.CVGaussianKilledRetryWarm
import Ttc.Exec.FiniteContinuingRetryProjectedZeroSafe
import Ttc.Exec.CVGaussianAcceptedWarm

/-! Zero-safe Gaussian random-fallback phase accuracy. -/

namespace Ttc.CVGaussianWarmFallbackZeroSafe

open MeasureTheory ProbabilityTheory Metric Set Pointwise
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.FiniteContinuingRetryEmbeddedSelective
open Ttc.FiniteContinuingRetryProjectedWarm
open Ttc.FiniteContinuingRetryProjectedZeroSafe
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVCombinedContinuingAccept Ttc.CVCombinedContinuingRetryPhaseTV
open Ttc.CVGaussianAcceptedWarm Ttc.CVContinuingRetryParameters
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- The Gaussian selective phase theorem without global survival or acceptance
nonzero assumptions.  Both are derived only on significant first-hit indices. -/
theorem tvLe_gaussianWarmFallbackPhase_selective_zeroSafe
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    (deadline : ENNReal → Nat) (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho]
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (L : Nat) {pi tau : Measure (State n)} [IsProbabilityMeasure tau]
    {M eta zeta : ENNReal} (heta0 : eta ≠ 0)
    (hwarm : ∀ i : Nat, IsWarm M
      (runningCurrent
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
      (sampleFromKernel (randomFallbackKernel fallback)
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
    have hsurv : augmentedSurvivalOf K hK delta s c hdelta hc steps rho i ≠ 0 := by
      exact ne_of_gt ((pos_iff_ne_zero.2 heta0).trans_le hi)
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
      hK hdelta hc deadline rho i
      heta0 (hwarm i) (by simpa only [steps] using hi) hmix
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
  apply tvLe_randomFallback_embeddedMarginal_selective_zeroSafe cand A
    (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
    (by intro a; simp [augmentedEmbedding, accepted]) rho L fallback target eta
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
      hK hdelta hc deadline rho j
      heta0 (hwarm j) (by
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

#print axioms tvLe_gaussianWarmFallbackPhase_selective_zeroSafe

end Ttc.CVGaussianWarmFallbackZeroSafe
