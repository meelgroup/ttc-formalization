import Ttc.Exec.FiniteContinuingRetryEmbeddedSelective
import Ttc.Exec.CVCombinedContinuingRetryPhaseTV
import Ttc.Exec.FiniteContinuingRetryGaussianAugmentedPhase
import Ttc.Exec.CVGaussianScoreSeedPhaseKernel

/-! Selective distributional TV for the variable-fallback Gaussian `(score, seed)` phase. -/

namespace Ttc.CVGaussianAugmentedSelectiveTV

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.FiniteContinuingRetry Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryEmbeddedSelective
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CVCombinedContinuingRetryPhaseTV
open Ttc.CVCombinedContinuingAccept Ttc.SpeedyRejection
open Ttc.CVGaussianScoreSeedPhaseKernel
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def augmentedMarginalOf
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (rho : Measure (ScoreSeed n)) (j : Nat) :=
  embeddedMarginal (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding rho j

noncomputable def augmentedSurvivalOf
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (rho : Measure (ScoreSeed n)) (j : Nat) :=
  embeddedSurvival (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding rho j

noncomputable def augmentedProposalOf
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (rho : Measure (ScoreSeed n)) (j : Nat) :=
  embeddedProposal (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding rho j

theorem sampleFrom_augmentedRetryStateKernel_eq_marginalOf
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho] (L : Nat) :
    Ttc.CVSequentialPhaseSampler.sampleFromKernel
        (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps L) rho =
      augmentedMarginalOf K hK delta s c hdelta hc steps rho L := by
  letI : IsProbabilityMeasure (Measure.map augmentedEmbedding rho) :=
    Measure.isProbabilityMeasure_map measurable_augmentedEmbedding.aemeasurable
  unfold Ttc.CVSequentialPhaseSampler.sampleFromKernel
    augmentedGaussianRetryStateKernel augmentedMarginalOf embeddedMarginal
  rw [Arlib.MarkovChains.bind_comap]
  exact Ttc.FiniteContinuingRetryGaussianPhaseKernel.sampleFromKernel_adaptiveKernel
    (augmentedGaussianRetrySchedule K hK delta s c hdelta hc steps)
    (Measure.map augmentedEmbedding rho) L

/-- The unresolved mass itself obeys the significant-survival bound used inside the
selective-TV argument.  Keeping this statement explicit lets a warm random fallback
pay only `survival * Mfb`, rather than the full fallback warmness `Mfb`. -/
theorem augmentedSurvivalOf_le_eta_add_pow
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    (steps : Nat → Nat) (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho]
    {eta r : ENNReal}
    (hs0 : ∀ j, augmentedSurvivalOf K hK delta s c hdelta hc steps rho j ≠ 0)
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤ augmentedSurvivalOf K hK delta s c hdelta hc steps rho j →
      augmentedProposalOf K hK delta s c hdelta hc steps rho j
        (costedCombinedAccept K c s)ᶜ ≤ r)
    (L : Nat) :
    augmentedSurvivalOf K hK delta s c hdelta hc steps rho L ≤ eta + r ^ L := by
  let candidate := phaseCandidate K hK delta s hdelta steps
  let A := costedCombinedAccept K c s
  let marginal := fun j ↦ embeddedMarginal candidate A
    (measurableSet_costedCombinedAccept hK hc) rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding rho j
  letI : ∀ j, IsProbabilityMeasure (marginal j) := fun j ↦
    isProbabilityMeasure_embeddedMarginal candidate A
      (measurableSet_costedCombinedAccept hK hc) rejectedNext measurable_rejectedNext
      (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
      roundQueryCost measurable_roundQueryCost augmentedEmbedding
      measurable_augmentedEmbedding rho j
  let proposal := fun j ↦ embeddedProposal candidate A
    (measurableSet_costedCombinedAccept hK hc) rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding rho j
  have hproposal : ∀ j, IsProbabilityMeasure (proposal j) := by
    intro j
    dsimp only [proposal, embeddedProposal, Ttc.CVSequentialPhaseSampler.sampleFromKernel]
    letI : IsProbabilityMeasure
        (condOn (marginal j) Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ (by
        simpa only [marginal, augmentedMarginalOf, augmentedSurvivalOf,
          embeddedSurvival, candidate, A] using hs0 j) (measure_ne_top _ _)
    letI : IsProbabilityMeasure
        ((condOn (marginal j) Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    infer_instance
  letI : ∀ j, IsProbabilityMeasure (proposal j) := hproposal
  let surv : Nat → ENNReal := fun j ↦ embeddedSurvival candidate A
    (measurableSet_costedCombinedAccept hK hc) rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding rho j
  have hbase : surv 0 ≤ 1 := prob_le_one
  have hmono : ∀ j, surv (j + 1) ≤ surv j := by
    intro j
    dsimp only [surv]
    rw [embeddedSurvival_succ candidate A (measurableSet_costedCombinedAccept hK hc)
      rejectedNext measurable_rejectedNext
      (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
      roundQueryCost measurable_roundQueryCost augmentedEmbedding
      measurable_augmentedEmbedding rho j (by
        simpa only [candidate, A, augmentedSurvivalOf] using hs0 j)]
    exact (mul_le_mul_left' prob_le_one _).trans_eq (mul_one _)
  have hcontract : ∀ j, eta ≤ surv j → surv (j + 1) ≤ r * surv j := by
    intro j hj
    dsimp only [surv] at hj ⊢
    rw [embeddedSurvival_succ candidate A (measurableSet_costedCombinedAccept hK hc)
      rejectedNext measurable_rejectedNext
      (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
      roundQueryCost measurable_roundQueryCost augmentedEmbedding
      measurable_augmentedEmbedding rho j (by
        simpa only [candidate, A, augmentedSurvivalOf] using hs0 j)]
    simpa only [proposal, candidate, A, augmentedProposalOf, mul_comm] using
      mul_le_mul_left'
        (hreject j (by simpa only [candidate, A, augmentedSurvivalOf] using hj))
        (surv j)
  have hmain := Ttc.ContinuingRejectionSignificant.survival_le_eta_add_pow
    surv hbase hr hmono hcontract L
  simpa only [surv, candidate, A, augmentedSurvivalOf] using hmain

/-- The actual augmented candidate at a significant retry is close to the ideal point/coin
candidate.  Only the seed/current marginal is used by the walk. -/
theorem tvLe_augmentedProposalOf_at_significant
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    (deadline : ENNReal → Nat) (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho]
    (j : Nat) {pi tau : Measure (State n)} [IsProbabilityMeasure tau]
    {M eta zeta : ENNReal} (heta0 : eta ≠ 0)
    (hwarm : IsWarm M
      ((augmentedMarginalOf K hK delta s c hdelta hc
        (fun _ ↦ deadline (M / eta)) rho j).map current) pi)
    (hsignificant : eta ≤ augmentedSurvivalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho j)
    (hmix : ∀ nu : Measure (State n),
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe
          (Ttc.CVSequentialPhaseSampler.sampleFromKernel
            (Ttc.CVSequentialPhaseSampler.iteratedKernel
              (lazy (speedyMetropolisGaussian K delta s)) (deadline (M / eta))) nu)
          tau zeta) :
    TVLe (Measure.map Prod.snd
      (augmentedProposalOf K hK delta s c hdelta hc
        (fun _ ↦ deadline (M / eta)) rho j))
      (SpeedyRejection.proposal tau) zeta := by
  let rhoJ := augmentedMarginalOf K hK delta s c hdelta hc
    (fun _ ↦ deadline (M / eta)) rho j
  haveI : IsProbabilityMeasure rhoJ :=
    isProbabilityMeasure_embeddedMarginal
      (phaseCandidate K hK delta s hdelta (fun _ ↦ deadline (M / eta)))
      (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
      rejectedNext measurable_rejectedNext
      (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
      roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
      rho j
  have hmain := tvLe_costErasedCandidate_at_significant hK hdelta deadline
    (rho := rhoJ) (pi := pi) (tau := tau) (last := current) measurable_current
    heta0 (by simpa only [rhoJ] using hwarm)
    (Survive := Ttc.FiniteContinuingRetry.runningStates)
    Ttc.FiniteContinuingRetry.measurableSet_runningStates (by
      change eta ≤ rhoJ Ttc.FiniteContinuingRetry.runningStates
      simpa only [rhoJ, augmentedMarginalOf, augmentedSurvivalOf, embeddedSurvival]
        using hsignificant) hmix
  simpa only [augmentedProposalOf, embeddedProposal, phaseCandidate, rhoJ,
    augmentedMarginalOf] using hmain

/-- Pair-valued selective TV capstone.  The unresolved branch returns its own incoming
`(score, seed)` pair; accepted branches lie on the exact graph `seed = c • score`. -/
theorem tvLe_actualGaussianAugmentedRetry_selective
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (deadline : ENNReal → Nat) (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho]
    (L : Nat) {pi tau : Measure (State n)} [IsProbabilityMeasure tau]
    {M eta r zeta : ENNReal} (heta0 : eta ≠ 0)
    (hs0 : ∀ j, augmentedSurvivalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho j ≠ 0)
    (ha0 : ∀ j, augmentedProposalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho j (costedCombinedAccept K c s) ≠ 0)
    (hwarm : ∀ i : Fin L, IsWarm M
      ((augmentedMarginalOf K hK delta s c hdelta hc
        (fun _ ↦ deadline (M / eta)) rho i).map current) pi)
    (hmix : ∀ nu : Measure (State n),
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe
          (Ttc.CVSequentialPhaseSampler.sampleFromKernel
            (Ttc.CVSequentialPhaseSampler.iteratedKernel
              (lazy (speedyMetropolisGaussian K delta s)) (deadline (M / eta))) nu)
          tau zeta)
    (hshrink : tau (c • K) ≠ 0)
    (hhalf : ENNReal.ofReal (1 / 2 : Real) ≤ tau (c • K))
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤
      (((Measure.map (fun y : State n ↦ c⁻¹ • y) (condOn tau (c • K))).withDensity
        (fun y ↦ ENNReal.ofReal (speedyAcceptReal c s y))) Set.univ))
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤ augmentedSurvivalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho j →
      augmentedProposalOf K hK delta s c hdelta hc
        (fun _ ↦ deadline (M / eta)) rho j (costedCombinedAccept K c s)ᶜ ≤ r) :
    TVLe (Measure.map output
      (augmentedMarginalOf K hK delta s c hdelta hc
        (fun _ ↦ deadline (M / eta)) rho L))
      (scoreSeedReference c
        (Measure.map (combinedOutput c)
          (condOn (SpeedyRejection.proposal tau) (combinedAccept K c s))))
      (32 * zeta + (eta + r ^ L)) := by
  have heighth : ENNReal.ofReal (1 / 8 : Real) ≤
      SpeedyRejection.proposal tau (combinedAccept K c s) :=
    proposal_combinedAccept_ge_eighth tau hK hc hs hc2 hshrink hhalf hquarter
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
  apply tvLe_map_output_embeddedMarginal_selective
    (phaseCandidate K hK delta s hdelta (fun _ ↦ deadline (M / eta)))
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
    (by intro a; simp [augmentedEmbedding, accepted]) rho L target eta r (32 * zeta)
  · exact hs0
  · exact ha0
  · intro i hi
    let rhoJ := augmentedMarginalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho i
    haveI : IsProbabilityMeasure rhoJ :=
      isProbabilityMeasure_embeddedMarginal
        (phaseCandidate K hK delta s hdelta (fun _ ↦ deadline (M / eta)))
        (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
        rejectedNext measurable_rejectedNext
        (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
        roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
        rho i
    have hsurv : rhoJ Ttc.FiniteContinuingRetry.runningStates ≠ 0 := by
      simpa only [rhoJ, augmentedMarginalOf, augmentedSurvivalOf, embeddedSurvival]
        using hs0 i
    letI : IsProbabilityMeasure (condOn rhoJ Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ hsurv (measure_ne_top _ _)
    letI : IsProbabilityMeasure
        ((condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    let p := augmentedProposalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho i
    letI : IsProbabilityMeasure p := by
      change IsProbabilityMeasure
        (Ttc.CVSequentialPhaseSampler.sampleFromKernel
          (phaseCandidate K hK delta s hdelta (fun _ ↦ deadline (M / eta)) i)
          ((condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current))
      infer_instance
    letI : IsProbabilityMeasure (Measure.map Prod.snd p) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    have hcand := tvLe_augmentedProposalOf_at_significant hK hdelta hc deadline rho i
      heta0 (hwarm i) hi hmix
    have hscore : TVLe
        (Measure.map (acceptedOutput c) (condOn p (costedCombinedAccept K c s)))
        targetScore (32 * zeta) := by
      rw [map_acceptedOutput_condOn_costedCombinedAccept
        (nu := p) (K := K) (c := c) (s := s) hK hc]
      exact (Ttc.ContinuingRejectionSignificant.tvLe_condOn_eighth
        (Measure.map Prod.snd p) (SpeedyRejection.proposal tau)
        (measurableSet_combinedAccept hK hc) hcand heighth hzeta).map
          (measurable_combinedOutput c)
    simpa only [p, augmentedProposalOf, target, targetScore, scoreSeedReference] using
      (tvLe_map_augmentedAcceptedOutput_of_score c hc hscore)
  · exact hr
  · exact hreject

#print axioms tvLe_actualGaussianAugmentedRetry_selective

end Ttc.CVGaussianAugmentedSelectiveTV
