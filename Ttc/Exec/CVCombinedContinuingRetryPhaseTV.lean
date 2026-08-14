import Ttc.Exec.FiniteContinuingRetryGaussian
import Ttc.Exec.FiniteContinuingRetryGeneralDecomposition

/-! Actual finite continuing-retry Gaussian phase: TV capstone. -/

namespace Ttc.CVCombinedContinuingRetryPhaseTV

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.FiniteContinuingRetry Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryGeneralDecomposition
open Ttc.FiniteContinuingRetryDecomposition
open Ttc.CVCombinedContinuingAccept Ttc.SpeedyRejection
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

noncomputable def phaseCandidate
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (steps : Nat → Nat) :
    Nat → Kernel (State n) (CostedCoin n) := fun j ↦
  combinedRoundCostedKernel K hK delta s hdelta (steps j)

instance phaseCandidate.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (steps : Nat → Nat) (j : Nat) :
    IsMarkovKernel (phaseCandidate K hK delta s hdelta steps j) := by
  unfold phaseCandidate
  infer_instance

noncomputable def phaseMarginal
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (x fallback : State n) (j : Nat) :=
  marginal (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (acceptedOutput c) (measurable_acceptedOutput c)
    roundQueryCost measurable_roundQueryCost x fallback j

noncomputable def phaseSurvival
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (x fallback : State n) (j : Nat) :=
  survival (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (acceptedOutput c) (measurable_acceptedOutput c)
    roundQueryCost measurable_roundQueryCost x fallback j

noncomputable def phaseProposal
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (x fallback : State n) (j : Nat) :=
  Ttc.FiniteContinuingRetryGeneralDecomposition.proposal
    (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (acceptedOutput c) (measurable_acceptedOutput c)
    roundQueryCost measurable_roundQueryCost x fallback j

/-- Erasing recorded query cost commutes with the combined acceptance normalization and
the accepted rescaling map. -/
theorem map_acceptedOutput_condOn_costedCombinedAccept
    (nu : Measure (CostedCoin n))
    {K : Set (State n)} (hK : MeasurableSet K) {c s : Real} (hc : c ≠ 0) :
    Measure.map (acceptedOutput c)
        (Arlib.condOn nu (costedCombinedAccept K c s)) =
      Measure.map (combinedOutput c)
        (Arlib.condOn (Measure.map Prod.snd nu) (combinedAccept K c s)) := by
  rw [← Ttc.CostedWarmPhaseRejection.map_condOn_preimage nu
    (measurableSet_combinedAccept hK hc)]
  rw [Measure.map_map (measurable_combinedOutput c) measurable_snd]
  rfl

/-- Significant-survival distributional mixing, specialized to the actual recorded-query
lazy-speedy candidate.  The cost-erasure identity is exact and adding the independent
uniform coin does not increase TV. -/
theorem tvLe_costErasedCandidate_at_significant
    {H : Type*} [MeasurableSpace H]
    {rho : Measure H} [IsProbabilityMeasure rho]
    {pi tau : Measure (State n)} [IsProbabilityMeasure tau]
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta s : Real} (hdelta : 0 < delta)
    (deadline : ENNReal → Nat)
    {last : H → State n} (hlast : Measurable last)
    {M eta zeta : ENNReal} (heta0 : eta ≠ 0)
    (hwarm : Arlib.IsWarm M (rho.map last) pi)
    {Survive : Set H} (hSurvive : MeasurableSet Survive)
    (hSurviveMass : eta ≤ rho Survive)
    (hmix : ∀ nu : Measure (State n),
      Arlib.IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        Arlib.TVLe
          (Ttc.CVSequentialPhaseSampler.sampleFromKernel
            (Ttc.CVSequentialPhaseSampler.iteratedKernel
              (lazy (speedyMetropolisGaussian K delta s)) (deadline (M / eta))) nu)
          tau zeta) :
    Arlib.TVLe
      (Measure.map Prod.snd
        (Ttc.CVSequentialPhaseSampler.sampleFromKernel
          (combinedRoundCostedKernel K hK delta s hdelta (deadline (M / eta)))
          ((Arlib.condOn rho Survive).map last)))
      (SpeedyRejection.proposal tau) zeta := by
  have hS0 : rho Survive ≠ 0 := by
    intro hzero
    have : eta = 0 := le_antisymm (by simpa [hzero] using hSurviveMass) bot_le
    exact heta0 this
  letI : IsProbabilityMeasure (Arlib.condOn rho Survive) :=
    Arlib.isProbabilityMeasure_condOn rho hS0 (measure_ne_top rho Survive)
  letI : IsProbabilityMeasure ((Arlib.condOn rho Survive).map last) :=
    Measure.isProbabilityMeasure_map hlast.aemeasurable
  have hpoint := Ttc.CVSignificantSurvivalWarm.tvLe_retry_at_distributionalWarmDeadline
    (fun t ↦ Ttc.CVSequentialPhaseSampler.iteratedKernel
      (lazy (speedyMetropolisGaussian K delta s)) t)
    deadline hlast heta0 hwarm hSurvive hSurviveMass hmix
  rw [map_snd_sampleFrom_combinedRoundCostedKernel hK delta s hdelta]
  have hpair := hpoint.prod (Arlib.TVLe.refl unitCoin)
  simpa only [SpeedyRejection.proposal, add_zero] using hpair

/-- Law-generic outer query cutoff transfer.  It is deliberately independent of how the
incoming retry-state law was produced, so it composes with a warm distributional initial
law rather than requiring pointwise/Dirac mixing. -/
theorem tvLe_queryCutoffOutput_target
    (mu : Measure (RetryState (State n) (State n))) [IsProbabilityMeasure mu]
    (fallback : State n) {cutoff etaQuery eps : ENNReal}
    (target : Measure (State n))
    (hcut0 : cutoff ≠ 0) (hcuttop : cutoff ≠ ⊤)
    (hmean : (∫⁻ z, accumulatedCost z ∂mu) / cutoff ≤ etaQuery)
    (hphase : Arlib.TVLe
      (Measure.map (Ttc.FiniteContinuingRetryDecomposition.cutoffOutput fallback) mu)
      target eps) :
    Arlib.TVLe (Measure.map (queryCutoffOutput fallback cutoff) mu)
      target (etaQuery + eps) :=
  (tvLe_queryCutoffOutput_of_lintegral_div_le
    mu fallback hcut0 hcuttop hmean).trans hphase

/-- Actual finite continuing-retry phase TV bound.  The only distributional premise is
the cost-erased candidate TV bound at each significant retry; the implementation itself
is the recorded-query lazy-speedy kernel. -/
theorem tvLe_actualGaussianRetryCutoff
    {K : Set (State n)} (hK : MeasurableSet K)
    {delta s c : Real} (hdelta : 0 < delta) (hc : c ≠ 0)
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1)
    (steps : Nat → Nat) (x fallback : State n) (L : Nat)
    (tau : Measure (State n)) [IsProbabilityMeasure tau]
    (eta r zeta : ENNReal)
    (hs0 : ∀ j, phaseSurvival K hK delta s c hdelta hc steps x fallback j ≠ 0)
    (ha0 : ∀ j, phaseProposal K hK delta s c hdelta hc steps x fallback j
      (costedCombinedAccept K c s) ≠ 0)
    (hcandidate : ∀ i : Fin L,
      Arlib.TVLe
        (Measure.map Prod.snd
          (phaseProposal K hK delta s c hdelta hc steps x fallback i))
        (SpeedyRejection.proposal tau) zeta)
    (hshrink : tau (c • K) ≠ 0)
    (hhalf : ENNReal.ofReal (1 / 2 : Real) ≤ tau (c • K))
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤
      (((Measure.map (fun y : State n ↦ c⁻¹ • y) (Arlib.condOn tau (c • K))).withDensity
        (fun y ↦ ENNReal.ofReal (speedyAcceptReal c s y))) Set.univ))
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤ phaseSurvival K hK delta s c hdelta hc steps x fallback j →
      phaseProposal K hK delta s c hdelta hc steps x fallback j
        (costedCombinedAccept K c s)ᶜ ≤ r) :
    Arlib.TVLe
      (Measure.map (cutoffOutput fallback)
        (phaseMarginal K hK delta s c hdelta hc steps x fallback L))
      (Measure.map (combinedOutput c)
        (Arlib.condOn (SpeedyRejection.proposal tau) (combinedAccept K c s)))
      (32 * zeta + (eta + r ^ L)) := by
  have heighth : ENNReal.ofReal (1 / 8 : Real) ≤
      SpeedyRejection.proposal tau (combinedAccept K c s) :=
    proposal_combinedAccept_ge_eighth tau hK hc hs hc2 hshrink hhalf hquarter
  have hideal0 : SpeedyRejection.proposal tau (combinedAccept K c s) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) heighth)
  letI : IsProbabilityMeasure
      (Arlib.condOn (SpeedyRejection.proposal tau) (combinedAccept K c s)) :=
    Arlib.isProbabilityMeasure_condOn _ hideal0 (measure_ne_top _ _)
  letI : IsProbabilityMeasure
      (Measure.map (combinedOutput c)
        (Arlib.condOn (SpeedyRejection.proposal tau) (combinedAccept K c s))) :=
    Measure.isProbabilityMeasure_map (measurable_combinedOutput c).aemeasurable
  apply tvLe_cutoffOutput_of_accepted
    (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (acceptedOutput c) (measurable_acceptedOutput c)
    roundQueryCost measurable_roundQueryCost x fallback L
    (Measure.map (combinedOutput c)
      (Arlib.condOn (SpeedyRejection.proposal tau) (combinedAccept K c s)))
    eta r (32 * zeta)
  · exact hs0
  · exact ha0
  · intro i
    let rhoJ : Measure (RetryState (State n) (State n)) :=
      marginal (phaseCandidate K hK delta s hdelta steps)
        (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
        rejectedNext measurable_rejectedNext
        (acceptedOutput c) (measurable_acceptedOutput c)
        roundQueryCost measurable_roundQueryCost x fallback i
    have hsurv : rhoJ Ttc.FiniteContinuingRetry.runningStates ≠ 0 := by
      simpa only [rhoJ, phaseSurvival,
        Ttc.FiniteContinuingRetryGeneralDecomposition.survival] using hs0 i
    letI : IsProbabilityMeasure rhoJ := by
      dsimp only [rhoJ]
      infer_instance
    letI : IsProbabilityMeasure
        (Arlib.condOn rhoJ
          Ttc.FiniteContinuingRetry.runningStates) :=
      Arlib.isProbabilityMeasure_condOn _ hsurv (measure_ne_top _ _)
    letI : IsProbabilityMeasure
        ((Arlib.condOn rhoJ
          Ttc.FiniteContinuingRetry.runningStates).map current) :=
      Measure.isProbabilityMeasure_map measurable_current.aemeasurable
    letI : IsProbabilityMeasure
        (phaseProposal K hK delta s c hdelta hc steps x fallback i) := by
      change IsProbabilityMeasure
        (Ttc.CVSequentialPhaseSampler.sampleFromKernel
          (phaseCandidate K hK delta s hdelta steps i)
          ((Arlib.condOn rhoJ Ttc.FiniteContinuingRetry.runningStates).map current))
      infer_instance
    letI : IsProbabilityMeasure
        (Measure.map Prod.snd
          (phaseProposal K hK delta s c hdelta hc steps x fallback i)) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    change Arlib.TVLe
      (Measure.map (acceptedOutput c)
        (Arlib.condOn
          (phaseProposal K hK delta s c hdelta hc steps x fallback i)
          (costedCombinedAccept K c s)))
      (Measure.map (combinedOutput c)
        (Arlib.condOn (SpeedyRejection.proposal tau) (combinedAccept K c s)))
      (32 * zeta)
    rw [map_acceptedOutput_condOn_costedCombinedAccept
      (nu := phaseProposal K hK delta s c hdelta hc steps x fallback i)
      (K := K) (c := c) (s := s) hK hc]
    exact (Ttc.ContinuingRejectionSignificant.tvLe_condOn_eighth
      (Measure.map Prod.snd
        (phaseProposal K hK delta s c hdelta hc steps x fallback i))
      (SpeedyRejection.proposal tau) (measurableSet_combinedAccept hK hc)
      (hcandidate i) heighth hzeta).map (measurable_combinedOutput c)
  · exact hr
  · exact hreject

#print axioms map_acceptedOutput_condOn_costedCombinedAccept
#print axioms tvLe_costErasedCandidate_at_significant
#print axioms tvLe_queryCutoffOutput_target
#print axioms tvLe_actualGaussianRetryCutoff

end Ttc.CVCombinedContinuingRetryPhaseTV
