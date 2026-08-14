import Ttc.Exec.CVGaussianWarmFallbackPhaseKernel

/-!
# Survival-weighted seed warmth for the Gaussian random fallback

The exact random-fallback decomposition retains the unresolved mass in front of the
fallback warmth constant.  This module combines that identity with the selective retry
survival estimate.  It is the form needed by a phase schedule: enough retries can make
`(eta + r ^ L) * Mfb` small even when the independently sampleable fallback itself has a
large warmness constant.
-/

namespace Ttc.CVGaussianWarmFallbackSurvivalBound

open MeasureTheory ProbabilityTheory
open Arlib
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryRandomFallback
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianWarmFallbackPhaseKernel
open scoped ENNReal

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- A phase-level seed-warmth theorem in which the random fallback is charged only by
the explicit significant-survival tail `eta + r^L`. -/
theorem isWarm_seed_gaussianWarmFallback_le_eta_add_pow
    {K : Set (State n)} (hK : MeasurableSet K) {delta s c : Real}
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat) (L : Nat)
    (fallback : Measure (ScoreSeed n)) [IsProbabilityMeasure fallback]
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (piNext : Measure (State n)) {Macc Mfb eta r : ENNReal}
    (hacc : IsWarm Macc
      (Measure.map Prod.snd
        (acceptedOutputSubmeasure
          (augmentedMarginalOf K hK delta s c hdelta hc steps
            (Measure.map (seedEmbedding c) rho) L))) piNext)
    (hfb : IsWarm Mfb (Measure.map Prod.snd fallback) piNext)
    (hs0 : ∀ j, augmentedSurvivalOf K hK delta s c hdelta hc steps
      (Measure.map (seedEmbedding c) rho) j ≠ 0)
    (hr : r ≤ 1)
    (hreject : ∀ j, eta ≤ augmentedSurvivalOf K hK delta s c hdelta hc steps
      (Measure.map (seedEmbedding c) rho) j →
      augmentedProposalOf K hK delta s c hdelta hc steps
        (Measure.map (seedEmbedding c) rho) j
          (Ttc.FiniteContinuingRetryGaussian.costedCombinedAccept K c s)ᶜ ≤ r) :
    IsWarm (Macc + (eta + r ^ L) * Mfb)
      (Measure.map Prod.snd
        (sampleFromKernel
          (gaussianWarmFallbackPhaseKernel K hK delta s c hdelta hc steps L fallback)
          rho)) piNext := by
  letI : IsProbabilityMeasure (Measure.map (seedEmbedding c) rho) :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  have hsurv :
      augmentedSurvivalOf K hK delta s c hdelta hc steps
          (Measure.map (seedEmbedding c) rho) L ≤ eta + r ^ L :=
    augmentedSurvivalOf_le_eta_add_pow hK hdelta hc steps
      (Measure.map (seedEmbedding c) rho) hs0 hr hreject L
  have hsharp := isWarm_seed_sampleFrom_gaussianWarmFallbackPhaseKernel_survival
    hK delta s c hdelta hc steps L fallback rho piNext hacc hfb
  apply hsharp.mono
  apply add_le_add (le_refl Macc)
  apply mul_le_mul_right'
  simpa only [augmentedSurvivalOf, augmentedMarginalOf,
    Ttc.FiniteContinuingRetryEmbeddedSelective.embeddedSurvival] using hsurv

#print axioms isWarm_seed_gaussianWarmFallback_le_eta_add_pow

end Ttc.CVGaussianWarmFallbackSurvivalBound
