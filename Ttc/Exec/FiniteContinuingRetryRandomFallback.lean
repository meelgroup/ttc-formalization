import Ttc.Exec.FiniteContinuingRetryEmbeddedSelective
import Arlib.Convexity.GaussianCooling.AdaptiveRestartWarm
import Ttc.Exec.CVGaussianScoreSeedPhaseKernel

/-! Independent random fallback postprocessing for a finite retry state. -/

namespace Ttc.FiniteContinuingRetryRandomFallback

open MeasureTheory ProbabilityTheory Set
open Arlib
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryDecomposition
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetrySelfSelective
open scoped ENNReal Classical

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- Return the stored accepted output, or on an unresolved state draw an independent
fallback from `fallbackLaw`. -/
noncomputable def randomFallbackKernel (fallbackLaw : Measure F)
    [IsProbabilityMeasure fallbackLaw] : Kernel (RetryState E F) F :=
  Kernel.piecewise measurableSet_acceptedStates
    (Kernel.deterministic (output : RetryState E F → F) measurable_output)
    (Kernel.const (RetryState E F) fallbackLaw)

instance randomFallbackKernel.isMarkovKernel (fallbackLaw : Measure F)
    [IsProbabilityMeasure fallbackLaw] :
    IsMarkovKernel (randomFallbackKernel (E := E) fallbackLaw) := by
  unfold randomFallbackKernel
  infer_instance

theorem randomFallbackKernel_apply (fallbackLaw : Measure F)
    [IsProbabilityMeasure fallbackLaw] (z : RetryState E F) :
    randomFallbackKernel fallbackLaw z =
      if accepted z = true then Measure.dirac (output z) else fallbackLaw := by
  rw [randomFallbackKernel, Kernel.piecewise_apply]
  by_cases hz : accepted z = true
  · rw [if_pos (by simpa [acceptedStates] using hz),
      Kernel.deterministic_apply measurable_output, if_pos hz]
  · rw [if_neg (by simpa [acceptedStates] using hz),
      Kernel.const_apply, if_neg hz]

noncomputable def acceptedOutputSubmeasure (mu : Measure (RetryState E F)) : Measure F :=
  Measure.map output (mu.restrict acceptedStates)

/-- Exact output law: accepted output sublaw plus survival mass times one fresh fallback
draw.  In particular no deterministic atom is introduced. -/
theorem sampleFrom_randomFallbackKernel
    (mu : Measure (RetryState E F)) [IsProbabilityMeasure mu]
    (fallbackLaw : Measure F) [IsProbabilityMeasure fallbackLaw] :
    sampleFromKernel (randomFallbackKernel fallbackLaw) mu =
      acceptedOutputSubmeasure mu + mu Ttc.FiniteContinuingRetry.runningStates • fallbackLaw := by
  ext T hT
  unfold sampleFromKernel
  rw [Measure.bind_apply hT (randomFallbackKernel fallbackLaw).aemeasurable]
  simp_rw [randomFallbackKernel_apply fallbackLaw]
  have hfun : (fun z : RetryState E F ↦
      (if accepted z = true then Measure.dirac (output z) else fallbackLaw) T) =
      acceptedStates.indicator (fun z ↦ T.indicator (1 : F → ENNReal) (output z)) +
        Ttc.FiniteContinuingRetry.runningStates.indicator (fun _ ↦ fallbackLaw T) := by
    funext z
    by_cases hz : accepted z = true <;>
      simp [hz, acceptedStates, Ttc.FiniteContinuingRetry.runningStates,
        Measure.dirac_apply' _ hT]
  rw [hfun]
  change (∫⁻ z,
    acceptedStates.indicator (fun z ↦ T.indicator (1 : F → ENNReal) (output z)) z +
      Ttc.FiniteContinuingRetry.runningStates.indicator (fun _ ↦ fallbackLaw T) z ∂mu) = _
  rw [lintegral_add_left]
  · have haccepted : (∫⁻ z,
        acceptedStates.indicator
          (fun z ↦ T.indicator (1 : F → ENNReal) (output z)) z ∂mu) =
        acceptedOutputSubmeasure mu T := by
      rw [acceptedOutputSubmeasure, Measure.map_apply measurable_output hT,
        Measure.restrict_apply (hT.preimage measurable_output)]
      rw [← lintegral_indicator_one
        ((hT.preimage measurable_output).inter measurableSet_acceptedStates)]
      apply lintegral_congr
      intro z
      by_cases ha : z ∈ (acceptedStates : Set (RetryState E F)) <;>
        by_cases ht : output z ∈ T <;> simp [ha, ht]
    have hrunning : (∫⁻ z,
        Ttc.FiniteContinuingRetry.runningStates.indicator
          (fun _ ↦ fallbackLaw T) z ∂mu) =
        mu Ttc.FiniteContinuingRetry.runningStates * fallbackLaw T := by
      rw [lintegral_indicator Ttc.FiniteContinuingRetry.measurableSet_runningStates,
        lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
      ac_rfl
    rw [haccepted, hrunning, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  · exact (((measurable_const.indicator hT).comp measurable_output).indicator
      measurableSet_acceptedStates)

/-- Selective accepted-mixture TV with an independent random unresolved fallback.  The
whole unresolved branch is charged by its survival mass, so no accuracy property of the
fallback law is needed. -/
theorem tvLe_sampleFrom_randomFallbackKernel_selective
    (mu : Measure (RetryState E F)) [IsProbabilityMeasure mu]
    (fallbackLaw target : Measure F)
    [IsProbabilityMeasure fallbackLaw] [IsProbabilityMeasure target]
    (L : Nat) (w : Fin L → ENNReal) (q : Fin L → Measure F)
    [∀ i, IsProbabilityMeasure (q i)]
    (delta eta : ENNReal) (Good : Fin L → Prop) [DecidablePred Good]
    (haccepted : acceptedOutputSubmeasure mu = ∑ i, w i • q i)
    (hmass : (∑ i, w i) + mu Ttc.FiniteContinuingRetry.runningStates = 1)
    (hq : ∀ i, Good i → TVLe (q i) target delta)
    (hbad : (∑ i with ¬ Good i, w i) +
      mu Ttc.FiniteContinuingRetry.runningStates ≤ eta) :
    TVLe (sampleFromKernel (randomFallbackKernel fallbackLaw) mu)
      target (delta + eta) := by
  rw [sampleFrom_randomFallbackKernel mu fallbackLaw, haccepted]
  apply tvLe_sum_smul_add_tail_selective L w q
    (mu Ttc.FiniteContinuingRetry.runningStates • fallbackLaw)
    target delta eta Good
  · simpa only [Measure.smul_apply, measure_univ, mul_one, smul_eq_mul] using hmass
  · exact hq
  · simpa only [Measure.smul_apply, measure_univ, mul_one, smul_eq_mul] using hbad

section Gaussian

open Arlib.GaussianCooling
open Ttc.CVGaussianScoreSeedPhaseKernel

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Independent cold restart, represented in the same `(score, seed)` state as an
accepted augmented phase. -/
noncomputable def coldScoreSeedFallback (c s0 radius : Real) : Measure (ScoreSeed n) :=
  Measure.map (seedEmbedding c) (coldBallStart (n := n) s0 radius)

theorem isProbabilityMeasure_coldScoreSeedFallback
    (c s0 radius : Real) (hs0 : 0 < s0) (hradius : 0 < radius) :
    IsProbabilityMeasure (coldScoreSeedFallback (n := n) c s0 radius) := by
  unfold coldScoreSeedFallback
  letI : IsProbabilityMeasure (coldBallStart (n := n) s0 radius) :=
    isProbabilityMeasure_coldBallStart hs0 hradius
  exact Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable

theorem map_snd_coldScoreSeedFallback (c s0 radius : Real) :
    Measure.map Prod.snd (coldScoreSeedFallback (n := n) c s0 radius) =
      coldBallStart (n := n) s0 radius := by
  rw [coldScoreSeedFallback, Measure.map_map measurable_snd (measurable_seedEmbedding c)]
  have hfun : Prod.snd ∘ seedEmbedding (n := n) c = id := by
    funext x
    rfl
  rw [hfun, Measure.map_id]

/-- Every proved adaptive cold-start warmness theorem transfers verbatim to the seed
coordinate of the independent random fallback. -/
theorem isWarm_snd_coldScoreSeedFallback
    (c s0 radius : Real) {pi : Measure (State n)} {M : ENNReal}
    (h : IsWarm M (coldBallStart (n := n) s0 radius) pi) :
    IsWarm M (Measure.map Prod.snd (coldScoreSeedFallback (n := n) c s0 radius)) pi := by
  rw [map_snd_coldScoreSeedFallback]
  exact h

#print axioms sampleFrom_randomFallbackKernel
#print axioms tvLe_sampleFrom_randomFallbackKernel_selective
#print axioms map_snd_coldScoreSeedFallback

end Gaussian

end Ttc.FiniteContinuingRetryRandomFallback
