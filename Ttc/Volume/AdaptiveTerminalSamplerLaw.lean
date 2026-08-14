/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AmbientGaussianRejection
import Ttc.Volume.CVPackedRun

/-!
# Branch-selected sampler laws including the terminal cooling coordinate

The terminal estimator has `m + 1` sampled ratios, indexed by `Fin (m + 1)`, but its cooling
chain also has length `m + 1`.  Thus coordinate `i` targets

`coolLaw (m + 1) sigmaSq K i`,

not `coolLaw (m + 2) ...`.  This file keeps that equality visible in every signature.

As in `AdaptivePhaseSamplerLaw`, a coordinate uses exact ambient-Gaussian membership
rejection while `4 * n * sigmaSq i <= 1`; otherwise it uses a supplied law intended to be
the eventual radius-`4` truncated-walk output.  The warm branch therefore exposes precisely
the supplied `TVLe` premise that the mixing theorem must later discharge.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open scoped ENNReal

variable {n r m k : Nat}

/-- One of the `m + 1` sampled laws of the terminal estimator. -/
noncomputable def adaptiveTerminalPhaseSamplerLaw
    (sigmaSq : Nat -> Real) (K : Set (Space n)) (i : Fin (m + 1))
    (truncatedLaw : Measure (Space n)) : Measure (Space n) :=
  if 4 * (n : Real) * sigmaSq i <= 1 then
    Measure.map (Ttc.CV.firstAcceptedDraw K)
      (roundsMeasure (Ttc.CV.ambientGaussianProb (n := n) (sigmaSq i)))
  else truncatedLaw

/-- The selected coordinate law is a probability measure when the supplied warm law is. -/
theorem isProbabilityMeasure_adaptiveTerminalPhaseSamplerLaw
    {sigmaSq : Nat -> Real} (hsigma : forall q, 0 < sigmaSq q)
    {K : Set (Space n)} (hKm : MeasurableSet K) (i : Fin (m + 1))
    (truncatedLaw : Measure (Space n)) [IsProbabilityMeasure truncatedLaw] :
    IsProbabilityMeasure (adaptiveTerminalPhaseSamplerLaw sigmaSq K i truncatedLaw) := by
  rw [adaptiveTerminalPhaseSamplerLaw]
  split_ifs
  · let proposal := Ttc.CV.ambientGaussianProb (n := n) (sigmaSq i)
    letI : IsProbabilityMeasure proposal :=
      Ttc.CV.isProbabilityMeasure_ambientGaussianProb (hsigma i)
    exact Measure.isProbabilityMeasure_map
      (Ttc.CV.measurable_firstAcceptedDraw hKm).aemeasurable
  · infer_instance

theorem adaptiveTerminalPhaseSamplerLaw_eq_rejection
    {sigmaSq : Nat -> Real} {K : Set (Space n)} {i : Fin (m + 1)}
    (truncatedLaw : Measure (Space n))
    (hcold : 4 * (n : Real) * sigmaSq i <= 1) :
    adaptiveTerminalPhaseSamplerLaw sigmaSq K i truncatedLaw =
      Measure.map (Ttc.CV.firstAcceptedDraw K)
        (roundsMeasure (Ttc.CV.ambientGaussianProb (n := n) (sigmaSq i))) := by
  simp [adaptiveTerminalPhaseSamplerLaw, hcold]

/-- **Correct terminal-chain target.**  A cold coordinate in `Fin (m + 1)` is exactly
`coolLaw (m + 1) sigmaSq K i`; no extra chain phase is introduced. -/
theorem adaptiveTerminalPhaseSamplerLaw_cold_eq_coolLaw
    {sigmaSq : Nat -> Real} (hsigma : forall q, 0 < sigmaSq q)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 <= n) (hball : closedBall (0 : Space n) 1 ⊆ K)
    (i : Fin (m + 1)) (truncatedLaw : Measure (Space n))
    (hcold : 4 * (n : Real) * sigmaSq i <= 1) :
    adaptiveTerminalPhaseSamplerLaw sigmaSq K i truncatedLaw =
      coolLaw (m + 1) sigmaSq K i := by
  rw [adaptiveTerminalPhaseSamplerLaw_eq_rejection truncatedLaw hcold]
  exact Ttc.CV.map_firstAcceptedDraw_ambientGaussian_eq_coolLaw_of_cold
    hsigma hKm hfin hn hball i.isLt hcold

theorem adaptiveTerminalPhaseSamplerLaw_cold_tv_zero
    {sigmaSq : Nat -> Real} (hsigma : forall q, 0 < sigmaSq q)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 <= n) (hball : closedBall (0 : Space n) 1 ⊆ K)
    (i : Fin (m + 1)) (truncatedLaw : Measure (Space n))
    (hcold : 4 * (n : Real) * sigmaSq i <= 1) :
    TVLe (adaptiveTerminalPhaseSamplerLaw sigmaSq K i truncatedLaw)
      (coolLaw (m + 1) sigmaSq K i) 0 := by
  rw [adaptiveTerminalPhaseSamplerLaw_cold_eq_coolLaw hsigma hKm hfin hn hball i
    truncatedLaw hcold]
  exact TVLe.refl _

/-- A supplied truncated-walk TV proof passes unchanged through the warm branch. -/
theorem adaptiveTerminalPhaseSamplerLaw_warm_tv
    {sigmaSq : Nat -> Real} {K : Set (Space n)} (i : Fin (m + 1))
    {truncatedLaw : Measure (Space n)} {b : ENNReal}
    (hwarm : ¬ 4 * (n : Real) * sigmaSq i <= 1)
    (hTV : TVLe truncatedLaw (coolLaw (m + 1) sigmaSq K i) b) :
    TVLe (adaptiveTerminalPhaseSamplerLaw sigmaSq K i truncatedLaw)
      (coolLaw (m + 1) sigmaSq K i) b := by
  simpa [adaptiveTerminalPhaseSamplerLaw, hwarm] using hTV

/-- Unified terminal-coordinate TV theorem: cold coordinates are exact, while warm
coordinates consume the supplied radius-`4` walk estimate. -/
theorem adaptiveTerminalPhaseSamplerLaw_tv
    {sigmaSq : Nat -> Real} (hsigma : forall q, 0 < sigmaSq q)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 <= n) (hball : closedBall (0 : Space n) 1 ⊆ K)
    (i : Fin (m + 1)) {truncatedLaw : Measure (Space n)} {b : ENNReal}
    (hWarmTV : ¬ 4 * (n : Real) * sigmaSq i <= 1 ->
      TVLe truncatedLaw (coolLaw (m + 1) sigmaSq K i) b) :
    TVLe (adaptiveTerminalPhaseSamplerLaw sigmaSq K i truncatedLaw)
      (coolLaw (m + 1) sigmaSq K i) b := by
  by_cases hcold : 4 * (n : Real) * sigmaSq i <= 1
  · exact (adaptiveTerminalPhaseSamplerLaw_cold_tv_zero hsigma hKm hfin hn hball i
      truncatedLaw hcold).mono zero_le
  · exact adaptiveTerminalPhaseSamplerLaw_warm_tv i hcold (hWarmTV hcold)

/-! ## The `r x (m + 1) x k` packed family -/

/-- The elementary law family in the exact shape used by the terminal coupling theorem. -/
noncomputable def adaptiveTerminalPackedSamplerFamily
    (sigmaSq : Nat -> Real) (K : Set (Space n))
    (truncatedLaw : Fin r -> Fin (m + 1) -> Fin k -> Measure (Space n)) :
    Fin r -> Fin (m + 1) -> Fin k -> Measure (Space n) :=
  fun t i l => adaptiveTerminalPhaseSamplerLaw sigmaSq K i (truncatedLaw t i l)

theorem isProbabilityMeasure_adaptiveTerminalPackedSamplerFamily
    {sigmaSq : Nat -> Real} (hsigma : forall q, 0 < sigmaSq q)
    {K : Set (Space n)} (hKm : MeasurableSet K)
    (truncatedLaw : Fin r -> Fin (m + 1) -> Fin k -> Measure (Space n))
    [htrunc : forall t i l, IsProbabilityMeasure (truncatedLaw t i l)]
    (t : Fin r) (i : Fin (m + 1)) (l : Fin k) :
    IsProbabilityMeasure
      (adaptiveTerminalPackedSamplerFamily sigmaSq K truncatedLaw t i l) := by
  exact isProbabilityMeasure_adaptiveTerminalPhaseSamplerLaw hsigma hKm i
    (truncatedLaw t i l)

/-- Consequently the packed outer run law is a probability measure. -/
theorem isProbabilityMeasure_adaptiveTerminalPackedRunLaw
    {sigmaSq : Nat -> Real} (hsigma : forall q, 0 < sigmaSq q)
    {K : Set (Space n)} (hKm : MeasurableSet K)
    (truncatedLaw : Fin r -> Fin (m + 1) -> Fin k -> Measure (Space n))
    [htrunc : forall t i l, IsProbabilityMeasure (truncatedLaw t i l)] :
    IsProbabilityMeasure (runMeasure
      (packedPhaseLaw (adaptiveTerminalPackedSamplerFamily sigmaSq K truncatedLaw))) := by
  letI : forall t i l, IsProbabilityMeasure
      (adaptiveTerminalPackedSamplerFamily sigmaSq K truncatedLaw t i l) :=
    fun t i l => isProbabilityMeasure_adaptiveTerminalPackedSamplerFamily hsigma hKm
      truncatedLaw t i l
  unfold runMeasure
  infer_instance

/-- Coordinatewise TV in the exact `Fin r -> Fin (m+1) -> Fin k` form consumed by
`CVTerminalCouplingAccuracy`, targeting the same `m+1`-length chain as the terminal exact
estimator. -/
theorem adaptiveTerminalPackedSamplerFamily_tv
    {sigmaSq : Nat -> Real} (hsigma : forall q, 0 < sigmaSq q)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 <= n) (hball : closedBall (0 : Space n) 1 ⊆ K)
    (truncatedLaw : Fin r -> Fin (m + 1) -> Fin k -> Measure (Space n)) {b : ENNReal}
    (hWarmTV : forall (t : Fin r) (i : Fin (m + 1)) (l : Fin k),
      ¬ 4 * (n : Real) * sigmaSq i <= 1 ->
      TVLe (truncatedLaw t i l) (coolLaw (m + 1) sigmaSq K i) b) :
    forall (t : Fin r) (i : Fin (m + 1)) (l : Fin k),
      TVLe (adaptiveTerminalPackedSamplerFamily sigmaSq K truncatedLaw t i l)
        (coolLaw (m + 1) sigmaSq K i) b := by
  intro t i l
  exact adaptiveTerminalPhaseSamplerLaw_tv hsigma hKm hfin hn hball i
    (hWarmTV t i l)

/-! ### Axiom audit -/

#print axioms adaptiveTerminalPhaseSamplerLaw_cold_eq_coolLaw
#print axioms adaptiveTerminalPhaseSamplerLaw_cold_tv_zero
#print axioms adaptiveTerminalPhaseSamplerLaw_warm_tv
#print axioms adaptiveTerminalPhaseSamplerLaw_tv
#print axioms isProbabilityMeasure_adaptiveTerminalPackedSamplerFamily
#print axioms isProbabilityMeasure_adaptiveTerminalPackedRunLaw
#print axioms adaptiveTerminalPackedSamplerFamily_tv

end Ttc.CVAdaptive
