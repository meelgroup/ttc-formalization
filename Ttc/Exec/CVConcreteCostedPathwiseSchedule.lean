import Ttc.Exec.CostedPathwisePhaseKernel
import Ttc.Exec.CVSourceOneRunFromCostedPhases

/-!
# The concrete costed pathwise CV phase schedule

This file connects the state-indexed implementation of the two rejection loops to the
generic source one-run/runtime assembly.  It deliberately leaves the two source acceptance
certificates explicit: they are exactly what makes each stopped loop terminate and what
turns the raw-walk query expectation into the factor-eight phase bound.
-/

namespace Ttc.CVConcreteCostedPathwiseSchedule

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.CostedPathwisePhaseKernel Ttc.CostedPathwisePhaseLumping
open Ttc.CVSourceOneRunFromCostedPhases
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State := EuclideanSpace Real (Fin n)

/-- The actual recorded-query implementation of every pathwise CV phase. -/
noncomputable def concreteCostedPhaseSchedule
    (K : Set (State (n := n))) (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (hdelta : forall i, 0 < delta i)
    (steps : Nat -> Nat) : Nat -> Kernel (State (n := n)) (ENNReal × State (n := n)) :=
  fun i => costedPathwisePhaseKernel K hK (delta i) (sigmaSq i) (hdelta i) (steps i)

instance concreteCostedPhaseSchedule.isMarkovKernel
    (K : Set (State (n := n))) (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (hdelta : forall i, 0 < delta i)
    (steps : Nat -> Nat) (i : Nat) :
    IsMarkovKernel (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps i) := by
  unfold concreteCostedPhaseSchedule
  infer_instance

/-- Under the two positive acceptance certificates, forgetting the recorded cost gives
exactly the statewise source phase transition used by the full-path accuracy theorem. -/
theorem map_snd_concreteCostedPhaseSchedule
    (K : Set (State (n := n))) (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (hdelta : forall i, 0 < delta i)
    (steps : Nat -> Nat) (hsigma : forall i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 <= 1)
    (hshrink : forall i x, 0 <
      iterate (lazy (speedyMetropolisGaussian K (delta i) (sigmaSq i)))
        (Measure.dirac x) (steps i) ((1 - 1 / (2 * (n : Real))) • K))
    (haccept : forall i x,
      ((Ttc.SpeedyRejection.phasePointProposal K (delta i) (sigmaSq i)
          (Measure.dirac x) (steps i)).withDensity
        (fun y => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (sigmaSq i) y))) Set.univ ≠ 0) :
    forall i x, Measure.map Prod.snd
        (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps i x) =
      pathwiseSourcePhaseSchedule K hK delta sigmaSq steps i x := by
  intro i x
  exact map_snd_costedPathwisePhaseKernel hK (delta i) (hdelta i) (steps i) x
    (hshrink i x) (hsigma i) hc2 (haccept i x)

/-- The factor-eight source accounting bound, pointwise at the incoming state. -/
theorem stepMean_concreteCostedPhaseSchedule_le_eight
    (K : Set (State (n := n))) (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (hdelta : forall i, 0 < delta i)
    (steps : Nat -> Nat) (hsigma : forall i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 <= 1)
    (hhalf : forall i x, ENNReal.ofReal (1 / 2 : Real) <=
      iterate (lazy (speedyMetropolisGaussian K (delta i) (sigmaSq i)))
        (Measure.dirac x) (steps i) ((1 - 1 / (2 * (n : Real))) • K))
    (hquarter : forall i x, ENNReal.ofReal (1 / 4 : Real) <=
      ((Ttc.SpeedyRejection.phasePointProposal K (delta i) (sigmaSq i)
          (Measure.dirac x) (steps i)).withDensity
        (fun y => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (sigmaSq i) y))) Set.univ) :
    forall i x, Ttc.SequentialCost.stepMean
        (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) i x <=
      8 * ∫⁻ omega,
        Ttc.RawGaussianLazyStoppedExecution.actualMembershipQueryCount (steps i) omega
        ∂(Ttc.RawGaussianLazyStoppedExecution.lazyRawStoppedExecution
          K hK (delta i) (sigmaSq i) (hdelta i) (Measure.dirac x)) := by
  intro i x
  exact lintegral_fst_costedPathwisePhaseKernel_le_eight hK (delta i) (hdelta i)
    (steps i) x (hhalf i x) (hquarter i x) (hsigma i) hc2

/-- Weakest concrete refinement package consumed by
`expectedQueryVolumeAlgorithmOfCostedPhases`.  Termination is pointwise, while cost is
bounded only after averaging under the actual incoming phase marginal. -/
theorem concreteCostedPhaseRefinement_of_phaseMeans
    (K : Set (State (n := n))) (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (hdelta : forall i, 0 < delta i)
    (steps : Nat -> Nat) (hsigma : forall i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 <= 1)
    (mu0 : Measure (State (n := n))) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat -> ENNReal)
    (hshrink : forall i x, 0 <
      iterate (lazy (speedyMetropolisGaussian K (delta i) (sigmaSq i)))
        (Measure.dirac x) (steps i) ((1 - 1 / (2 * (n : Real))) • K))
    (haccept : forall i x,
      ((Ttc.SpeedyRejection.phasePointProposal K (delta i) (sigmaSq i)
          (Measure.dirac x) (steps i)).withDensity
        (fun y => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (sigmaSq i) y))) Set.univ ≠ 0)
    (hphaseMean : forall i, i < m ->
      (∫⁻ x, Ttc.SequentialCost.stepMean
          (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) i x
        ∂costedPhaseStateMarginal
          (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) mu0 i) <=
        phaseBound i) :
    CostedPhaseKernelRefinement
      (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps)
      (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps)
      mu0 m phaseBound := by
  refine { forgetCost := ?_, phaseMean := hphaseMean }
  exact map_snd_concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps hsigma hc2
    hshrink haccept

/-- A stronger convenient corollary using pointwise half/quarter acceptance.  The main
source-faithful interface is `concreteCostedPhaseRefinement_of_phaseMeans`; this theorem
must not be used to infer a pointwise bound merely from a distributional warm start. -/
theorem concreteCostedPhaseRefinement
    (K : Set (State (n := n))) (hK : MeasurableSet K)
    (delta sigmaSq : Nat -> Real) (hdelta : forall i, 0 < delta i)
    (steps : Nat -> Nat) (hsigma : forall i, 0 < sigmaSq i)
    (hc2 : (1 - 1 / (2 * (n : Real))) ^ 2 <= 1)
    (mu0 : Measure (State (n := n))) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat -> ENNReal)
    (hhalf : forall i x, ENNReal.ofReal (1 / 2 : Real) <=
      iterate (lazy (speedyMetropolisGaussian K (delta i) (sigmaSq i)))
        (Measure.dirac x) (steps i) ((1 - 1 / (2 * (n : Real))) • K))
    (hquarter : forall i x, ENNReal.ofReal (1 / 4 : Real) <=
      ((Ttc.SpeedyRejection.phasePointProposal K (delta i) (sigmaSq i)
          (Measure.dirac x) (steps i)).withDensity
        (fun y => ENNReal.ofReal
          (speedyAcceptReal (1 - 1 / (2 * (n : Real))) (sigmaSq i) y))) Set.univ)
    (hrawMean : forall i, i < m ->
      (∫⁻ x, 8 * ∫⁻ omega,
          Ttc.RawGaussianLazyStoppedExecution.actualMembershipQueryCount (steps i) omega
          ∂(Ttc.RawGaussianLazyStoppedExecution.lazyRawStoppedExecution
            K hK (delta i) (sigmaSq i) (hdelta i) (Measure.dirac x))
        ∂costedPhaseStateMarginal
          (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) mu0 i) <=
        phaseBound i) :
    CostedPhaseKernelRefinement
      (pathwiseSourcePhaseSchedule K hK delta sigmaSq steps)
      (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps)
      mu0 m phaseBound := by
  refine { forgetCost := ?_, phaseMean := ?_ }
  · apply map_snd_concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps
      hsigma hc2
    · intro i x
      exact (ENNReal.ofReal_pos.mpr (by norm_num)).trans_le (hhalf i x)
    · intro i x
      exact ((ENNReal.ofReal_pos.mpr (by norm_num)).trans_le (hquarter i x)).ne'
  · intro i hi
    calc
      (∫⁻ x, Ttc.SequentialCost.stepMean
          (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) i x
          ∂costedPhaseStateMarginal
            (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) mu0 i) <=
          ∫⁻ x, 8 * ∫⁻ omega,
            Ttc.RawGaussianLazyStoppedExecution.actualMembershipQueryCount (steps i) omega
            ∂(Ttc.RawGaussianLazyStoppedExecution.lazyRawStoppedExecution
              K hK (delta i) (sigmaSq i) (hdelta i) (Measure.dirac x))
            ∂costedPhaseStateMarginal
              (concreteCostedPhaseSchedule K hK delta sigmaSq hdelta steps) mu0 i :=
        lintegral_mono (stepMean_concreteCostedPhaseSchedule_le_eight K hK delta
          sigmaSq hdelta steps hsigma hc2 hhalf hquarter i)
      _ <= phaseBound i := hrawMean i hi

#print axioms map_snd_concreteCostedPhaseSchedule
#print axioms stepMean_concreteCostedPhaseSchedule_le_eight
#print axioms concreteCostedPhaseRefinement_of_phaseMeans
#print axioms concreteCostedPhaseRefinement

end Ttc.CVConcreteCostedPathwiseSchedule
