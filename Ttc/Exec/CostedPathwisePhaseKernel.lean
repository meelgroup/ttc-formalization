import Ttc.Exec.StatewiseCostedRejectionKernel
import Ttc.Exec.CostedStatefulSpeedyPhases

/-! A measurable, state-indexed costed realization of the two-rejection phase kernel. -/

namespace Ttc.CostedPathwisePhaseKernel

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CostedWarmPhaseRejection Ttc.CostedStatefulSpeedyPhases
open Ttc.StatewiseCostedRejectionKernel Ttc.SpeedyRejection
open Ttc.CVPathwisePhaseKernel
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

theorem speedyPhaseCostedKernel_apply_eq_walkEndpointCostLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) (x : State n) :
    speedyPhaseCostedKernel K hK delta s hdelta t x =
      walkEndpointCostLaw K hK delta s hdelta (Measure.dirac x) t := by
  have hout : Measurable (fun omega : Nat → ENNReal × State n =>
      (Ttc.SequentialCost.totalCost t omega, (omega t).2)) :=
    (Ttc.SequentialCost.measurable_totalCost t).prodMk
      (measurable_snd.comp (measurable_pi_apply t))
  unfold speedyPhaseCostedKernel walkEndpointCostLaw
  rw [Kernel.map_apply _ hout]
  rw [← Ttc.SequentialCost.execution_dirac
    (Ttc.RawGaussianLazyStoppedExecution.lazyRawStoppedSchedule
      K hK delta s hdelta) x]
  rfl

/-- First stopped loop, followed by the source shrink-factor rescaling. -/
noncomputable def pathwisePhasePointCostKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) : Kernel (State n) (ENNReal × State n) :=
  let c : Real := 1 - 1 / (2 * (n : Real))
  Kernel.map
    (costedRejectionKernel
      (speedyPhaseCostedKernel K hK delta s hdelta t) (c • K)
      (measurableSet_smul_set hK
        (Ttc.CostedWarmPhaseRejection.shrinkFactor_ne_zero n)))
    (fun z : ENNReal × State n => (z.1, c⁻¹ • z.2))

instance pathwisePhasePointCostKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) :
    IsMarkovKernel (pathwisePhasePointCostKernel K hK delta s hdelta t) := by
  unfold pathwisePhasePointCostKernel
  dsimp only
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem pathwisePhasePointCostKernel_apply_eq
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) (x : State n) :
    pathwisePhasePointCostKernel K hK delta s hdelta t x =
      phasePointCostLaw K hK delta s hdelta (Measure.dirac x) t := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hcK : MeasurableSet (c • K) := measurableSet_smul_set hK
    (Ttc.CostedWarmPhaseRejection.shrinkFactor_ne_zero n)
  rw [pathwisePhasePointCostKernel, Kernel.map_apply _ (by fun_prop),
    costedRejectionKernel_apply_eq _ (c • K) hcK
      (iidRoundsIdentified _) x,
    speedyPhaseCostedKernel_apply_eq_walkEndpointCostLaw hK delta s hdelta t x]
  rfl

/-- Add the independent zero-query uniform coin to a state-indexed point-cost kernel. -/
noncomputable def pathwiseSpeedyRoundCostKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) :
    Kernel (State n) (ENNReal × (State n × Real)) :=
  let rho := pathwisePhasePointCostKernel K hK delta s hdelta t
  Kernel.map
    (Kernel.compProd rho
      (Kernel.const (State n × (ENNReal × State n)) unitCoin))
    (fun p : (ENNReal × State n) × Real =>
      (p.1.1, (p.1.2, p.2)))

instance pathwiseSpeedyRoundCostKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) :
    IsMarkovKernel (pathwiseSpeedyRoundCostKernel K hK delta s hdelta t) := by
  unfold pathwiseSpeedyRoundCostKernel
  dsimp only
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem pathwiseSpeedyRoundCostKernel_apply_eq
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) (x : State n) :
    pathwiseSpeedyRoundCostKernel K hK delta s hdelta t x =
      costedSpeedyRoundLaw
        (phasePointCostLaw K hK delta s hdelta (Measure.dirac x) t) := by
  let rho := pathwisePhasePointCostKernel K hK delta s hdelta t
  have hprod : (Kernel.compProd rho
      (Kernel.const (State n × (ENNReal × State n)) unitCoin)) x =
      (rho x).prod unitCoin := by
    calc
      _ = (rho x) ⊗ₘ Kernel.const (ENNReal × State n) unitCoin := by
        ext S hS
        rw [Kernel.compProd_apply hS]
        rw [Measure.compProd_apply hS]
        rfl
      _ = _ := Measure.compProd_const
  rw [pathwiseSpeedyRoundCostKernel, Kernel.map_apply _ (by fun_prop), hprod]
  rw [pathwisePhasePointCostKernel_apply_eq hK delta s hdelta t x]
  unfold costedSpeedyRoundLaw
  rfl

/-- The two stopped loops as one genuine Markov kernel of the incoming state. -/
noncomputable def costedPathwisePhaseKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) : Kernel (State n) (ENNReal × State n) :=
  let c : Real := 1 - 1 / (2 * (n : Real))
  Kernel.map
    (costedRejectionKernel
      (pathwiseSpeedyRoundCostKernel K hK delta s hdelta t)
      (acceptRegion c s) (measurableSet_acceptRegion c s))
    (fun z : ENNReal × (State n × Real) => (z.1, z.2.1))

instance costedPathwisePhaseKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) :
    IsMarkovKernel (costedPathwisePhaseKernel K hK delta s hdelta t) := by
  unfold costedPathwisePhaseKernel
  dsimp only
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem costedPathwisePhaseKernel_apply_eq_warmPhaseCostLaw
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real)
    (hdelta : 0 < delta) (t : Nat) (x : State n) :
    costedPathwisePhaseKernel K hK delta s hdelta t x =
      warmPhaseCostLaw K hK delta s hdelta (Measure.dirac x) t := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hA : MeasurableSet (acceptRegion (n := n) c s) :=
    measurableSet_acceptRegion c s
  rw [costedPathwisePhaseKernel, Kernel.map_apply _ (by fun_prop),
    costedRejectionKernel_apply_eq _ (acceptRegion c s) hA
      (iidRoundsIdentified _) x,
    pathwiseSpeedyRoundCostKernel_apply_eq hK delta s hdelta t x]
  rfl

/-- Exact state marginal: the operational two-loop cost kernel is the statewise-normalized
pathwise phase transition on every input where both source rejection masses are positive. -/
theorem map_snd_costedPathwisePhaseKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) {s : Real}
    (hdelta : 0 < delta) (t : Nat) (x : State n)
    (hshrink : 0 < iterate (lazy (speedyMetropolisGaussian K delta s))
      (Measure.dirac x) t ((1 - 1 / (2 * (n : Real))) • K))
    (hs : 0 < s) (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1)
    (hmass : ((phasePointProposal K delta s (Measure.dirac x) t).withDensity
      (fun y => ENNReal.ofReal
        (speedyAcceptReal (1 - 1 / (2 * (n : Real))) s y))) Set.univ ≠ 0) :
    Measure.map Prod.snd
        (costedPathwisePhaseKernel K hK delta s hdelta t x) =
      pathwisePhaseKernel K hK delta s t x := by
  rw [costedPathwisePhaseKernel_apply_eq_warmPhaseCostLaw hK delta s hdelta t x,
    map_snd_warmPhaseCostLaw_eq_phaseLaw hK delta hdelta
      (Measure.dirac x) t hshrink hs hc2 hmass]
  exact (pathwisePhaseKernel_apply_eq_phaseLaw_dirac K hK delta t x
    (pos_iff_ne_zero.mp hshrink) hmass).symm

/-- Exact conditional expected recorded-query cost of the state-indexed two-loop phase. -/
theorem lintegral_fst_costedPathwisePhaseKernel
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) {s : Real}
    (hdelta : 0 < delta) (t : Nat) (x : State n)
    (hshrink : 0 < iterate (lazy (speedyMetropolisGaussian K delta s))
      (Measure.dirac x) t ((1 - 1 / (2 * (n : Real))) • K))
    (hs : 0 < s) (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    ∫⁻ z, z.1 ∂(costedPathwisePhaseKernel K hK delta s hdelta t x) =
      ((phasePointProposal K delta s (Measure.dirac x) t).withDensity
          (fun y => ENNReal.ofReal
            (speedyAcceptReal (1 - 1 / (2 * (n : Real))) s y)) Set.univ)⁻¹ *
      (iterate (lazy (speedyMetropolisGaussian K delta s))
        (Measure.dirac x) t ((1 - 1 / (2 * (n : Real))) • K))⁻¹ *
      ∫⁻ omega, Ttc.RawGaussianLazyStoppedExecution.actualMembershipQueryCount t omega
        ∂(Ttc.RawGaussianLazyStoppedExecution.lazyRawStoppedExecution
          K hK delta s hdelta (Measure.dirac x)) := by
  rw [costedPathwisePhaseKernel_apply_eq_warmPhaseCostLaw hK delta s hdelta t x]
  exact lintegral_fst_warmPhaseCostLaw hK delta hdelta
    (Measure.dirac x) t hshrink hs hc2

/-- Under the source half-mass and quarter-mass certificates, the two statewise restart
loops multiply the expected recorded membership-query count by at most eight. -/
theorem lintegral_fst_costedPathwisePhaseKernel_le_eight
    {K : Set (State n)} (hK : MeasurableSet K) (delta : Real) {s : Real}
    (hdelta : 0 < delta) (t : Nat) (x : State n)
    (hhalf : ENNReal.ofReal (1 / 2 : Real) ≤
      iterate (lazy (speedyMetropolisGaussian K delta s))
        (Measure.dirac x) t ((1 - 1 / (2 * (n : Real))) • K))
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤
      ((phasePointProposal K delta s (Measure.dirac x) t).withDensity
        (fun y => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) s y))) Set.univ)
    (hs : 0 < s) (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 ≤ 1) :
    ∫⁻ z, z.1 ∂(costedPathwisePhaseKernel K hK delta s hdelta t x) ≤
      8 * ∫⁻ omega,
        Ttc.RawGaussianLazyStoppedExecution.actualMembershipQueryCount t omega
        ∂(Ttc.RawGaussianLazyStoppedExecution.lazyRawStoppedExecution
          K hK delta s hdelta (Measure.dirac x)) := by
  rw [costedPathwisePhaseKernel_apply_eq_warmPhaseCostLaw hK delta s hdelta t x]
  exact lintegral_fst_warmPhaseCostLaw_le_eight hK delta hdelta
    (Measure.dirac x) t hhalf hquarter hs hc2

#print axioms map_snd_costedPathwisePhaseKernel
#print axioms lintegral_fst_costedPathwisePhaseKernel
#print axioms lintegral_fst_costedPathwisePhaseKernel_le_eight

end Ttc.CostedPathwisePhaseKernel
