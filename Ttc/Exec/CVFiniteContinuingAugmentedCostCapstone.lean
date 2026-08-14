import Ttc.Exec.FiniteContinuingRetryGaussianAugmentedPhase
import Ttc.Exec.GenericCostedPhaseCertificate

/-! Phase-family cost refinement for the augmented continuing-retry state. -/

namespace Ttc.CVFiniteContinuingAugmentedCostCapstone

open MeasureTheory ProbabilityTheory
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.GenericCostedPhaseCertificate
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev AugmentedState (n : Nat) := State n × State n

noncomputable def augmentedCostedSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) :
    Nat → Kernel (AugmentedState n) (ENNReal × AugmentedState n) := fun i ↦
  augmentedGaussianFinitePhaseCostedKernel K hK (delta i) (sigmaSq i) (shrink i)
    (hdelta i) (hshrink i) (retrySteps i) (retries i)

instance augmentedCostedSchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    IsMarkovKernel
      (augmentedCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries i) := by
  unfold augmentedCostedSchedule
  infer_instance

noncomputable def augmentedStateSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) :
    Nat → Kernel (AugmentedState n) (AugmentedState n) := fun i ↦
  Kernel.map
    (augmentedCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries i) Prod.snd

instance augmentedStateSchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    IsMarkovKernel
      (augmentedStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries i) := by
  unfold augmentedStateSchedule
  exact Kernel.IsMarkovKernel.map _ measurable_snd

theorem map_snd_augmentedCostedSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (a : AugmentedState n) :
    Measure.map Prod.snd
      (augmentedCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries i a) =
      augmentedStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries i a := by
  unfold augmentedStateSchedule
  rw [Kernel.map_apply _ measurable_snd]

/-- The augmented operational family is a generic costed refinement once its actual
incoming-marginal query means are bounded.  The per-phase exact identification with
`augmentedPhaseQueryMean` is
`lintegral_stepMean_augmentedGaussianFinitePhaseCostedKernel`. -/
theorem augmentedRefinement
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu0 : Measure (AugmentedState n)) [IsProbabilityMeasure mu0]
    (m : Nat) (phaseBound : Nat → ENNReal)
    (hphase : ∀ i, i < m →
      (∫⁻ a, Ttc.SequentialCost.stepMean
        (augmentedCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries) i a
        ∂stateMarginal
          (augmentedCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries) mu0 i) ≤ phaseBound i) :
    Refinement
      (augmentedStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries)
      (augmentedCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries) mu0 m phaseBound where
  forgetCost := map_snd_augmentedCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
    retrySteps retries
  phaseMean := hphase

#print axioms augmentedRefinement

end Ttc.CVFiniteContinuingAugmentedCostCapstone
