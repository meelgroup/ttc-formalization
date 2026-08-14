/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CVGaussianAugmentedSelectiveTV
import Ttc.Exec.FiniteContinuingRetryProjectedWarm

/-!
# Significant retry mixing from the killed running submeasure

The continuing-retry analysis only samples from the history conditioned on still running.
It therefore suffices to dominate the *unnormalised killed running submeasure*.  Requiring
the full retry-state current marginal to remain warm also includes already-accepted,
absorbing states and is unnecessarily strong.
-/

namespace Ttc.CVGaussianKilledRetryWarm

open MeasureTheory ProbabilityTheory
open Arlib Arlib.MarkovChains
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.FiniteContinuingRetryEmbeddedSelective
open Ttc.CVCombinedContinuingRetryPhaseTV
open Ttc.CVGaussianAugmentedSelectiveTV
open scoped ENNReal Classical

/-- Normalising a killed submeasure of mass at least `eta` costs at most `eta⁻¹` in
warmness.  This is the subprobability form needed by continuing retries. -/
theorem isWarm_map_condOn_of_killed
    {H E : Type*} [MeasurableSpace H] [MeasurableSpace E]
    {rho : Measure H} {pi : Measure E} {last : H → E}
    (hlast : Measurable last) {M eta : ENNReal}
    {S : Set H} (hS : MeasurableSet S)
    (hwarm : IsWarm M (Measure.map last (rho.restrict S)) pi)
    (hmass : eta ≤ rho S) :
    IsWarm (M / eta) (Measure.map last (condOn rho S)) pi := by
  intro T hT
  have hw := hwarm T hT
  rw [Measure.map_apply hlast hT, Measure.restrict_apply (hT.preimage hlast)] at hw
  rw [Measure.map_apply hlast hT, condOn_apply rho hS (hT.preimage hlast)]
  calc
    rho (last ⁻¹' T ∩ S) / rho S = rho (last ⁻¹' T ∩ S) * (rho S)⁻¹ :=
      div_eq_mul_inv _ _
    _ ≤ (M * pi T) * (rho S)⁻¹ := mul_le_mul_right' hw _
    _ ≤ (M * pi T) * eta⁻¹ := by
      gcongr
    _ = (M / eta) * pi T := by
      rw [div_eq_mul_inv]
      ac_rfl

/-- Distributional warm mixing from a significant event, assuming warmth only for the
unnormalised killed history submeasure. -/
theorem tvLe_costErasedCandidate_at_significant_killed
    {n : Nat} {H : Type*} [MeasurableSpace H]
    {rho : Measure H} [IsProbabilityMeasure rho]
    {pi tau : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure tau]
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta s : Real} (hdelta : 0 < delta)
    (deadline : ENNReal → Nat)
    {last : H → EuclideanSpace Real (Fin n)} (hlast : Measurable last)
    {M eta zeta : ENNReal} (heta0 : eta ≠ 0)
    {Survive : Set H} (hSurvive : MeasurableSet Survive)
    (hwarm : IsWarm M (Measure.map last (rho.restrict Survive)) pi)
    (hSurviveMass : eta ≤ rho Survive)
    (hmix : ∀ nu : Measure (EuclideanSpace Real (Fin n)),
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe
          (sampleFromKernel
            (iteratedKernel (lazy (speedyMetropolisGaussian K delta s))
              (deadline (M / eta))) nu)
          tau zeta) :
    TVLe
      (Measure.map Prod.snd
        (sampleFromKernel
          (Ttc.FiniteContinuingRetryGaussian.combinedRoundCostedKernel
            K hK delta s hdelta (deadline (M / eta)))
          ((condOn rho Survive).map last)))
      (Ttc.SpeedyRejection.proposal tau) zeta := by
  have hS0 : rho Survive ≠ 0 := by
    intro hzero
    apply heta0
    exact le_antisymm (by simpa [hzero] using hSurviveMass) bot_le
  letI : IsProbabilityMeasure (condOn rho Survive) :=
    Arlib.isProbabilityMeasure_condOn rho hS0 (measure_ne_top rho Survive)
  letI : IsProbabilityMeasure ((condOn rho Survive).map last) :=
    Measure.isProbabilityMeasure_map hlast.aemeasurable
  have hstart : IsWarm (M / eta) ((condOn rho Survive).map last) pi :=
    isWarm_map_condOn_of_killed hlast hSurvive hwarm hSurviveMass
  have hpoint := hmix _ hstart inferInstance
  rw [Ttc.FiniteContinuingRetryGaussian.map_snd_sampleFrom_combinedRoundCostedKernel
    hK delta s hdelta]
  have hpair := hpoint.prod (TVLe.refl Ttc.SpeedyRejection.unitCoin)
  simpa only [Ttc.SpeedyRejection.proposal, add_zero] using hpair

/-- Gaussian augmented-proposal specialization of the killed-submeasure theorem. -/
theorem tvLe_augmentedProposalOf_at_significant_killed
    {n : Nat} {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    (deadline : ENNReal → Nat)
    (rho : Measure (Ttc.CVGaussianAugmentedSelectiveTV.ScoreSeed n))
    [IsProbabilityMeasure rho] (j : Nat)
    {pi tau : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure tau]
    {M eta zeta : ENNReal} (heta0 : eta ≠ 0)
    (hwarm : IsWarm M
      (Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent
        (Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf K hK delta s c
          hdelta hc (fun _ ↦ deadline (M / eta)) rho j)) pi)
    (hsignificant : eta ≤
      Ttc.CVGaussianAugmentedSelectiveTV.augmentedSurvivalOf K hK delta s c
        hdelta hc (fun _ ↦ deadline (M / eta)) rho j)
    (hmix : ∀ nu : Measure (EuclideanSpace Real (Fin n)),
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe
          (sampleFromKernel
            (iteratedKernel (lazy (speedyMetropolisGaussian K delta s))
              (deadline (M / eta))) nu)
          tau zeta) :
    TVLe (Measure.map Prod.snd
      (Ttc.CVGaussianAugmentedSelectiveTV.augmentedProposalOf K hK delta s c
        hdelta hc (fun _ ↦ deadline (M / eta)) rho j))
      (Ttc.SpeedyRejection.proposal tau) zeta := by
  let rhoJ := Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf
    K hK delta s c hdelta hc (fun _ ↦ deadline (M / eta)) rho j
  haveI : IsProbabilityMeasure rhoJ :=
    isProbabilityMeasure_embeddedMarginal
      (phaseCandidate K hK delta s hdelta
        (fun _ ↦ deadline (M / eta)))
      (costedCombinedAccept K c s)
      (measurableSet_costedCombinedAccept hK hc)
      rejectedNext measurable_rejectedNext
      (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
      roundQueryCost measurable_roundQueryCost
      augmentedEmbedding measurable_augmentedEmbedding rho j
  have hmain := tvLe_costErasedCandidate_at_significant_killed hK hdelta deadline
    (rho := rhoJ) (pi := pi) (tau := tau)
    (last := Ttc.FiniteContinuingRetry.current)
    Ttc.FiniteContinuingRetry.measurable_current heta0
    (Survive := Ttc.FiniteContinuingRetry.runningStates)
    Ttc.FiniteContinuingRetry.measurableSet_runningStates
    (by simpa only [rhoJ, Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf,
        Ttc.FiniteContinuingRetryProjectedWarm.runningCurrent] using hwarm)
    (by
      change eta ≤ rhoJ Ttc.FiniteContinuingRetry.runningStates
      simpa only [rhoJ, Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf,
        Ttc.CVGaussianAugmentedSelectiveTV.augmentedSurvivalOf,
        Ttc.FiniteContinuingRetryEmbeddedSelective.embeddedSurvival] using hsignificant)
    hmix
  simpa only [Ttc.CVGaussianAugmentedSelectiveTV.augmentedProposalOf,
    Ttc.FiniteContinuingRetryEmbeddedSelective.embeddedProposal,
    phaseCandidate, rhoJ,
    Ttc.CVGaussianAugmentedSelectiveTV.augmentedMarginalOf] using hmain

#print axioms isWarm_map_condOn_of_killed
#print axioms tvLe_costErasedCandidate_at_significant_killed
#print axioms tvLe_augmentedProposalOf_at_significant_killed

end Ttc.CVGaussianKilledRetryWarm
