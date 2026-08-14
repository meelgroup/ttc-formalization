import Ttc.Exec.CVGaussianWarmFallbackPhaseKernel
import Ttc.Exec.CVFiniteAugmentedSeedOperational

/-! Sequential seed-projected operation for Gaussian phases with independent warm fallback. -/

namespace Ttc.CVGaussianWarmFallbackOperational

open MeasureTheory ProbabilityTheory
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVGaussianWarmFallbackPhaseKernel
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVSeedProjectedDependence
open Ttc.CVFiniteAugmentedSeedOperational
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.CVGaussianAugmentedSelectiveTV
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Phase family with a caller-supplied independent warm fallback law. -/
noncomputable def warmFallbackSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] :
    Nat → Kernel (State n) (ScoreSeed n) := fun i ↦
  gaussianWarmFallbackPhaseKernel K hK (delta i) (sigmaSq i) (shrink i)
    (hdelta i) (hshrink i) (retrySteps i) (retries i) (fallback i)

instance warmFallbackSchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries fallback i) := by
  unfold warmFallbackSchedule
  infer_instance

/-- Accepted-sublaw warmth plus the independent fallback closes the complete seed step.
This is the precise point at which the deterministic/self fallback obstruction disappears. -/
theorem isWarm_seed_warmFallbackSchedule_step
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    (pi : Nat → Measure (State n))
    (warmBudget acceptedBudget fallbackBudget : Nat → ENNReal)
    (haccepted : ∀ i (rho : Measure (State n)), IsProbabilityMeasure rho →
      IsWarm (warmBudget i) rho (pi i) →
        IsWarm (acceptedBudget i)
          (Measure.map Prod.snd
            (acceptedOutputSubmeasure
              (augmentedMarginalOf K hK (delta i) (sigmaSq i) (shrink i)
                (hdelta i) (hshrink i) (retrySteps i)
                (Measure.map (seedEmbedding (shrink i)) rho) (retries i))))
          (pi (i + 1)))
    (hfallback : ∀ i,
      IsWarm (fallbackBudget i) (Measure.map Prod.snd (fallback i)) (pi (i + 1)))
    (hgrowth : ∀ i,
      acceptedBudget i + fallbackBudget i ≤ warmBudget (i + 1))
    (i : Nat) (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (hrho : IsWarm (warmBudget i) rho (pi i)) :
    IsWarm (warmBudget (i + 1))
      (Measure.map Prod.snd
        (sampleFromKernel
          (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries fallback i) rho)) (pi (i + 1)) := by
  exact (isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel hK
    (delta i) (sigmaSq i) (shrink i) (hdelta i) (hshrink i)
    (retrySteps i) (retries i) (fallback i) rho (pi (i + 1))
    (haccepted i rho inferInstance hrho) (hfallback i)).mono (hgrowth i)

/-- Full corrected-dependence package for the honest random-fallback schedule.  The only
remaining analytic phase inputs are warmth of the accepted seed sublaw and selective TV
mixing of the complete score/seed phase. -/
noncomputable def seedProjectedOperational_of_warmFallback
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (fallback : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (fallback i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real) (m : Nat) (eta : Real)
    (pi : Nat → Measure (State n)) (tau : Nat → Measure (ScoreSeed n))
    [∀ i, IsProbabilityMeasure (tau i)]
    (warmBudget acceptedBudget fallbackBudget mixError : Nat → ENNReal)
    (hstart : IsWarm (warmBudget 0) (Measure.map Prod.snd mu0) (pi 0))
    (haccepted : ∀ i (rho : Measure (State n)), IsProbabilityMeasure rho →
      IsWarm (warmBudget i) rho (pi i) →
        IsWarm (acceptedBudget i)
          (Measure.map Prod.snd
            (acceptedOutputSubmeasure
              (augmentedMarginalOf K hK (delta i) (sigmaSq i) (shrink i)
                (hdelta i) (hshrink i) (retrySteps i)
                (Measure.map (seedEmbedding (shrink i)) rho) (retries i))))
          (pi (i + 1)))
    (hfallback : ∀ i,
      IsWarm (fallbackBudget i) (Measure.map Prod.snd (fallback i)) (pi (i + 1)))
    (hgrowth : ∀ i,
      acceptedBudget i + fallbackBudget i ≤ warmBudget (i + 1))
    (hmixTop : ∀ i, mixError i ≠ ⊤)
    (hmix : ∀ i (rho : Measure (State n)),
      IsWarm (2 * warmBudget i) rho (pi i) → IsProbabilityMeasure rho →
        TVLe
          (sampleFromKernel
            (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries fallback i) rho)
          (tau i) (mixError i))
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i,
      accuracyU
          (inhomogeneousPathMeasure
            (stateScheduleFromSeed
              (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
                retrySteps retries fallback)) mu0)
          V (Ttc.CVCorrected.correctedAlpha m eta) i =
        fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1)
    (hbudget : ∀ i,
      2 * (mixError i).toReal ≤ Ttc.CVCorrected.correctedNu m eta) :
    SeedProjectedOperational
      (stateScheduleFromSeed
        (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries fallback))
      (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries fallback)
      Prod.snd Prod.fst mu0 V m eta :=
  seedProjectedOperational_of_recurrence
    (warmFallbackSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries fallback)
    mu0 V m eta pi tau warmBudget mixError hstart
    (fun i rho hprob hrho ↦ by
      letI : IsProbabilityMeasure rho := hprob
      exact isWarm_seed_warmFallbackSchedule_step K hK delta sigmaSq shrink hdelta
        hshrink retrySteps retries fallback pi warmBudget acceptedBudget fallbackBudget
        haccepted hfallback hgrowth i rho hrho)
    hmixTop hmix u v hu hv hU hV hbudget

#print axioms isWarm_seed_warmFallbackSchedule_step
#print axioms seedProjectedOperational_of_warmFallback

end Ttc.CVGaussianWarmFallbackOperational
