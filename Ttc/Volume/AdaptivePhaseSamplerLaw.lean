/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.AmbientGaussianRejection
import Ttc.Volume.CVPackedRun

/-!
# Branch-selected laws for the adaptive Gaussian-cooling sampler

At phase `i`, the operational sampler uses direct ambient-Gaussian membership rejection
while `4 * n * sigmaSq i <= 1`.  Outside that range it uses a supplied law, intended to be
the output law of the radius-`4` truncated walk.  Keeping the latter as an explicit argument
isolates the only theorem still needed from the mixing development: a coordinatewise `TVLe`
bound.  It does not hide an exact-law oracle in the warm branch.

The last section repeats this choice at every `(run, phase, sample)` coordinate and packages
the resulting independent product law in exactly the shape consumed by
`CVAdaptiveOracleAccuracy`.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open scoped ENNReal

variable {n r m k : Nat}

/-- One adaptive phase sampler law.  `truncatedLaw` is the eventual radius-`4` walk output
law; it is selected only after ambient rejection leaves the constant-acceptance regime. -/
noncomputable def adaptivePhaseSamplerLaw
    (N s0 : Real) (K : Set (Space n)) (i : Fin m)
    (truncatedLaw : Measure (Space n)) : Measure (Space n) :=
  if 4 * (n : Real) * adaptiveSigmaSq N s0 i <= 1 then
    Measure.map (Ttc.CV.firstAcceptedDraw K)
      (roundsMeasure (Ttc.CV.ambientGaussianProb (n := n) (adaptiveSigmaSq N s0 i)))
  else truncatedLaw

/-- The branch-selected law is a probability measure whenever the supplied truncated-walk
law is.  The cold branch uses the actual measurable stopping map over i.i.d. proposals. -/
theorem isProbabilityMeasure_adaptivePhaseSamplerLaw
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (i : Fin m)
    (truncatedLaw : Measure (Space n)) [IsProbabilityMeasure truncatedLaw] :
    IsProbabilityMeasure (adaptivePhaseSamplerLaw N s0 K i truncatedLaw) := by
  rw [adaptivePhaseSamplerLaw]
  split_ifs
  · let proposal := Ttc.CV.ambientGaussianProb (n := n) (adaptiveSigmaSq N s0 i)
    letI : IsProbabilityMeasure proposal :=
      Ttc.CV.isProbabilityMeasure_ambientGaussianProb (adaptiveSigmaSq_pos hN hs0 i)
    exact Measure.isProbabilityMeasure_map
      (Ttc.CV.measurable_firstAcceptedDraw hKm).aemeasurable
  · infer_instance

/-- In the cold branch, the chosen law is definitionally the ambient rejection output. -/
theorem adaptivePhaseSamplerLaw_eq_rejection
    {N s0 : Real} {K : Set (Space n)} {i : Fin m}
    (truncatedLaw : Measure (Space n))
    (hcold : 4 * (n : Real) * adaptiveSigmaSq N s0 i <= 1) :
    adaptivePhaseSamplerLaw N s0 K i truncatedLaw =
      Measure.map (Ttc.CV.firstAcceptedDraw K)
        (roundsMeasure
          (Ttc.CV.ambientGaussianProb (n := n) (adaptiveSigmaSq N s0 i))) := by
  simp [adaptivePhaseSamplerLaw, hcold]

/-- The cold branch is exactly the adaptive cooling law, with zero total-variation error. -/
theorem adaptivePhaseSamplerLaw_cold_eq_coolLaw
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 <= n) (hball : closedBall (0 : Space n) 1 ⊆ K)
    (i : Fin m) (truncatedLaw : Measure (Space n))
    (hcold : 4 * (n : Real) * adaptiveSigmaSq N s0 i <= 1) :
    adaptivePhaseSamplerLaw N s0 K i truncatedLaw =
      coolLaw (m + 1) (adaptiveSigmaSq N s0) K i := by
  rw [adaptivePhaseSamplerLaw_eq_rejection truncatedLaw hcold]
  exact Ttc.CV.map_firstAcceptedDraw_ambientGaussian_eq_coolLaw_of_cold
    (fun j => adaptiveSigmaSq_pos hN hs0 j) hKm hfin hn hball
    (by omega : (i : Nat) < m + 1) hcold

theorem adaptivePhaseSamplerLaw_cold_tv_zero
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 <= n) (hball : closedBall (0 : Space n) 1 ⊆ K)
    (i : Fin m) (truncatedLaw : Measure (Space n))
    (hcold : 4 * (n : Real) * adaptiveSigmaSq N s0 i <= 1) :
    TVLe (adaptivePhaseSamplerLaw N s0 K i truncatedLaw)
      (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i) 0 := by
  rw [adaptivePhaseSamplerLaw_cold_eq_coolLaw hN hs0 hKm hfin hn hball i
    truncatedLaw hcold]
  exact TVLe.refl _

/-- Warm-branch adapter: any supplied radius-`4` truncated-walk TV theorem transports
verbatim through the branch selector. -/
theorem adaptivePhaseSamplerLaw_warm_tv
    {N s0 : Real} {K : Set (Space n)} (i : Fin m)
    {truncatedLaw : Measure (Space n)} {b : ENNReal}
    (hwarm : ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i <= 1)
    (hTV : TVLe truncatedLaw (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i) b) :
    TVLe (adaptivePhaseSamplerLaw N s0 K i truncatedLaw)
      (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i) b := by
  simpa [adaptivePhaseSamplerLaw, hwarm] using hTV

/-- Unified single-coordinate interface: cold coordinates are exact; only warm coordinates
need a supplied TV proof. -/
theorem adaptivePhaseSamplerLaw_tv
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 <= n) (hball : closedBall (0 : Space n) 1 ⊆ K)
    (i : Fin m) {truncatedLaw : Measure (Space n)} {b : ENNReal}
    (hWarmTV : ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i <= 1 ->
      TVLe truncatedLaw (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i) b) :
    TVLe (adaptivePhaseSamplerLaw N s0 K i truncatedLaw)
      (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i) b := by
  by_cases hcold : 4 * (n : Real) * adaptiveSigmaSq N s0 i <= 1
  · exact (adaptivePhaseSamplerLaw_cold_tv_zero hN hs0 hKm hfin hn hball i
      truncatedLaw hcold).mono zero_le
  · exact adaptivePhaseSamplerLaw_warm_tv i hcold (hWarmTV hcold)

/-! ## Packed independent family -/

/-- Repeat the branch selection independently at all `r * m * k` elementary coordinates. -/
noncomputable def adaptivePackedSamplerFamily
    (N s0 : Real) (K : Set (Space n))
    (truncatedLaw : Fin r -> Fin m -> Fin k -> Measure (Space n)) :
    Fin r -> Fin m -> Fin k -> Measure (Space n) :=
  fun t i l => adaptivePhaseSamplerLaw N s0 K i (truncatedLaw t i l)

/-- Every elementary coordinate of the packed family is a probability measure. -/
theorem isProbabilityMeasure_adaptivePackedSamplerFamily
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K)
    (truncatedLaw : Fin r -> Fin m -> Fin k -> Measure (Space n))
    [htrunc : ∀ t i l, IsProbabilityMeasure (truncatedLaw t i l)]
    (t : Fin r) (i : Fin m) (l : Fin k) :
    IsProbabilityMeasure (adaptivePackedSamplerFamily N s0 K truncatedLaw t i l) := by
  exact isProbabilityMeasure_adaptivePhaseSamplerLaw hN hs0 hKm i (truncatedLaw t i l)

/-- The outer run law over packed phase vectors is itself a probability measure. -/
theorem isProbabilityMeasure_adaptivePackedRunLaw
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K)
    (truncatedLaw : Fin r -> Fin m -> Fin k -> Measure (Space n))
    [htrunc : ∀ t i l, IsProbabilityMeasure (truncatedLaw t i l)] :
    IsProbabilityMeasure
      (runMeasure (packedPhaseLaw (adaptivePackedSamplerFamily N s0 K truncatedLaw))) := by
  letI : ∀ t i l, IsProbabilityMeasure
      (adaptivePackedSamplerFamily N s0 K truncatedLaw t i l) :=
    fun t i l => isProbabilityMeasure_adaptivePackedSamplerFamily hN hs0 hKm
      truncatedLaw t i l
  unfold runMeasure
  infer_instance

/-- Coordinatewise TV interface in precisely the shape required by
`CVAdaptiveOracleAccuracy.packed_median_accuracy_adaptive_of_tv`. -/
theorem adaptivePackedSamplerFamily_tv
    {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {K : Set (Space n)} (hKm : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hn : 1 <= n) (hball : closedBall (0 : Space n) 1 ⊆ K)
    (truncatedLaw : Fin r -> Fin m -> Fin k -> Measure (Space n)) {b : ENNReal}
    (hWarmTV : ∀ (t : Fin r) (i : Fin m) (l : Fin k),
      ¬ 4 * (n : Real) * adaptiveSigmaSq N s0 i <= 1 ->
      TVLe (truncatedLaw t i l)
        (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i) b) :
    ∀ (t : Fin r) (i : Fin m) (l : Fin k),
      TVLe (adaptivePackedSamplerFamily N s0 K truncatedLaw t i l)
      (coolLaw (m + 1) (adaptiveSigmaSq N s0) K i) b := by
  intro t i l
  exact adaptivePhaseSamplerLaw_tv hN hs0 hKm hfin hn hball i
    (hWarmTV t i l)

/-! ### Axiom audit -/

#print axioms adaptivePhaseSamplerLaw_cold_eq_coolLaw
#print axioms adaptivePhaseSamplerLaw_cold_tv_zero
#print axioms adaptivePhaseSamplerLaw_warm_tv
#print axioms adaptivePhaseSamplerLaw_tv
#print axioms isProbabilityMeasure_adaptivePackedSamplerFamily
#print axioms isProbabilityMeasure_adaptivePackedRunLaw
#print axioms adaptivePackedSamplerFamily_tv

end Ttc.CVAdaptive
