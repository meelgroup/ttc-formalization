import Ttc.Exec.FiniteContinuingRetryInitialMeasure
import Ttc.Exec.CVCombinedContinuingRetryPhaseTV

/-! Distributional-initial-law TV theorem for the continuing Gaussian retry phase. -/

namespace Ttc.CVCombinedContinuingRetryDistributionalTV

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.FiniteContinuingRetry Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryInitialMeasure
open Ttc.CVCombinedContinuingRetryPhaseTV
open Ttc.CVCombinedContinuingAccept Ttc.SpeedyRejection
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def phaseMarginalOf
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (rho : Measure (State n)) (fallback : State n) (j : Nat) :=
  marginalOf (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (acceptedOutput c) (measurable_acceptedOutput c)
    roundQueryCost measurable_roundQueryCost rho fallback j

noncomputable def phaseSurvivalOf
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (rho : Measure (State n)) (fallback : State n) (j : Nat) :=
  survivalOf (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (acceptedOutput c) (measurable_acceptedOutput c)
    roundQueryCost measurable_roundQueryCost rho fallback j

noncomputable def phaseProposalOf
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (rho : Measure (State n)) (fallback : State n) (j : Nat) :=
  proposalOf (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (acceptedOutput c) (measurable_acceptedOutput c)
    roundQueryCost measurable_roundQueryCost rho fallback j

/-- At a significant retry, distributional warm mixing of the lazy-speedy endpoint gives
the required TV estimate for the actual cost-erased point/coin candidate. -/
theorem tvLe_phaseProposalOf_at_significant
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    (deadline : ENNReal → Nat) (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (fallback : State n) (j : Nat)
    {pi tau : Measure (State n)} [IsProbabilityMeasure tau]
    {M eta zeta : ENNReal} (heta0 : eta ≠ 0)
    (hwarm : IsWarm M
      ((phaseMarginalOf K hK delta s c hdelta hc
        (fun _ ↦ deadline (M / eta)) rho fallback j).map current) pi)
    (hsignificant : eta ≤ phaseSurvivalOf K hK delta s c hdelta hc
      (fun _ ↦ deadline (M / eta)) rho fallback j)
    (hmix : ∀ nu : Measure (State n),
      IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe
          (Ttc.CVSequentialPhaseSampler.sampleFromKernel
            (Ttc.CVSequentialPhaseSampler.iteratedKernel
              (lazy (speedyMetropolisGaussian K delta s)) (deadline (M / eta))) nu)
          tau zeta) :
    TVLe
      (Measure.map Prod.snd
        (phaseProposalOf K hK delta s c hdelta hc
          (fun _ ↦ deadline (M / eta)) rho fallback j))
      (SpeedyRejection.proposal tau) zeta := by
  let rhoJ := phaseMarginalOf K hK delta s c hdelta hc
    (fun _ ↦ deadline (M / eta)) rho fallback j
  have hJprob : IsProbabilityMeasure rhoJ := by
    dsimp only [rhoJ, phaseMarginalOf]
    infer_instance
  letI : IsProbabilityMeasure rhoJ := hJprob
  have hmain := tvLe_costErasedCandidate_at_significant hK hdelta deadline
    (rho := rhoJ) (pi := pi) (tau := tau) (last := current) measurable_current
    heta0 (by simpa only [rhoJ] using hwarm)
    (Survive := Ttc.FiniteContinuingRetry.runningStates)
    measurableSet_runningStates (by
      change eta ≤ rhoJ Ttc.FiniteContinuingRetry.runningStates
      simpa only [rhoJ, phaseMarginalOf, phaseSurvivalOf, survivalOf] using hsignificant) hmix
  simpa only [phaseProposalOf, proposalOf, phaseCandidate, rhoJ, phaseMarginalOf] using hmain

/-- Source-faithful finite retry TV theorem from an arbitrary warm incoming phase law. -/
theorem tvLe_actualGaussianRetryCutoff_initialLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (steps : Nat → Nat) (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (fallback : State n) (L : Nat)
    (tau : Measure (State n)) [IsProbabilityMeasure tau]
    (eta r zeta : ENNReal)
    (hs0 : ∀ j, phaseSurvivalOf K hK delta s c hdelta hc steps rho fallback j ≠ 0)
    (ha0 : ∀ j, phaseProposalOf K hK delta s c hdelta hc steps rho fallback j
      (costedCombinedAccept K c s) ≠ 0)
    (hcandidate : ∀ i : Fin L, TVLe
      (Measure.map Prod.snd
        (phaseProposalOf K hK delta s c hdelta hc steps rho fallback i))
      (SpeedyRejection.proposal tau) zeta)
    (hshrink : tau (c • K) ≠ 0)
    (hhalf : ENNReal.ofReal (1 / 2 : Real) ≤ tau (c • K))
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤
      (((Measure.map (fun y : State n ↦ c⁻¹ • y) (condOn tau (c • K))).withDensity
        (fun y ↦ ENNReal.ofReal (speedyAcceptReal c s y))) Set.univ))
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤ phaseSurvivalOf K hK delta s c hdelta hc steps rho fallback j →
      phaseProposalOf K hK delta s c hdelta hc steps rho fallback j
        (costedCombinedAccept K c s)ᶜ ≤ r) :
    TVLe
      (Measure.map (Ttc.FiniteContinuingRetryDecomposition.cutoffOutput fallback)
        (phaseMarginalOf K hK delta s c hdelta hc steps rho fallback L))
      (Measure.map (combinedOutput c)
        (condOn (SpeedyRejection.proposal tau) (combinedAccept K c s)))
      (32 * zeta + (eta + r ^ L)) := by
  have heighth : ENNReal.ofReal (1 / 8 : Real) ≤
      SpeedyRejection.proposal tau (combinedAccept K c s) :=
    proposal_combinedAccept_ge_eighth tau hK hc hs hc2 hshrink hhalf hquarter
  have hideal0 : SpeedyRejection.proposal tau (combinedAccept K c s) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) heighth)
  let target := Measure.map (combinedOutput c)
    (condOn (SpeedyRejection.proposal tau) (combinedAccept K c s))
  letI : IsProbabilityMeasure
      (condOn (SpeedyRejection.proposal tau) (combinedAccept K c s)) :=
    Arlib.isProbabilityMeasure_condOn _ hideal0 (measure_ne_top _ _)
  letI : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map (measurable_combinedOutput c).aemeasurable
  apply tvLe_cutoffOutput_of_accepted_initialLaw
    (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (acceptedOutput c) (measurable_acceptedOutput c)
    roundQueryCost measurable_roundQueryCost rho fallback L target eta r (32 * zeta)
  · exact hs0
  · exact ha0
  · intro i
    let rhoJ := phaseMarginalOf K hK delta s c hdelta hc steps rho fallback i
    have hJprob : IsProbabilityMeasure rhoJ := by
      dsimp only [rhoJ, phaseMarginalOf]
      infer_instance
    letI : IsProbabilityMeasure rhoJ := hJprob
    have hsurv : rhoJ Ttc.FiniteContinuingRetry.runningStates ≠ 0 := by
      simpa only [rhoJ, phaseMarginalOf, phaseSurvivalOf, survivalOf] using hs0 i
    letI : IsProbabilityMeasure
        (condOn rhoJ Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ hsurv (measure_ne_top _ _)
    letI : IsProbabilityMeasure
        ((condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    letI : IsProbabilityMeasure
        (phaseProposalOf K hK delta s c hdelta hc steps rho fallback i) := by
      change IsProbabilityMeasure
        (Ttc.CVSequentialPhaseSampler.sampleFromKernel
          (phaseCandidate K hK delta s hdelta steps i)
          ((condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current))
      infer_instance
    letI : IsProbabilityMeasure
        (Measure.map Prod.snd
          (phaseProposalOf K hK delta s c hdelta hc steps rho fallback i)) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    change TVLe
      (Measure.map (acceptedOutput c)
        (condOn (phaseProposalOf K hK delta s c hdelta hc steps rho fallback i)
          (costedCombinedAccept K c s))) target (32 * zeta)
    rw [Ttc.CVCombinedContinuingRetryPhaseTV.map_acceptedOutput_condOn_costedCombinedAccept
      (nu := phaseProposalOf K hK delta s c hdelta hc steps rho fallback i)
      (K := K) (c := c) (s := s) hK hc]
    exact (Ttc.ContinuingRejectionSignificant.tvLe_condOn_eighth
      (Measure.map Prod.snd
        (phaseProposalOf K hK delta s c hdelta hc steps rho fallback i))
      (SpeedyRejection.proposal tau) (measurableSet_combinedAccept hK hc)
      (hcandidate i) heighth hzeta).map (measurable_combinedOutput c)
  · exact hr
  · exact hreject

#print axioms tvLe_phaseProposalOf_at_significant
#print axioms tvLe_actualGaussianRetryCutoff_initialLaw

end Ttc.CVCombinedContinuingRetryDistributionalTV
