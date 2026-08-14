/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.PolynomialBallWalkKV97Sampler
import Ttc.Sampler.SpeedyBackend
import Arlib.Lattice.KV97.InflateGeom
import Arlib.MarkovChains.Continuous.SpeedyAffine

/-!
# Cost-preserving affine normalization for the explicit KV97 ball-walk sampler

The recorded walk is run on the normalized preimage
`{y | cen + gamma * y in K}` and only its final endpoint is mapped back.  Consequently a
normalized-body membership test is definitionally the original membership test after one
affine arithmetic operation, and the recorded membership-query count is unchanged.

For a KV97-inflated polytope, the normalized radius bound simplifies exactly to the
original aspect ratio `D / gamma`: inflation enlarges the inball and diameter by cancelling
factors.  The canonical uniform-inball warm start currently has only the explicit bound
`(D / gamma)^n`.  This file records that bound rather than calling it polynomial: it is
exponential in the dimension unless additional rounding supplies a polynomial warm start.
-/

namespace Ttc.AffinePolynomialBallWalkKV97Sampler

open MeasureTheory ProbabilityTheory Metric Set Function
open Arlib Arlib.MarkovChains
open Ttc.PolynomialBallWalkKV97Sampler
open scoped ENNReal Classical

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- The inverse normalization chart, from normalized to original coordinates. -/
abbrev chart (cen : State n) (gamma : Real) (y : State n) : State n :=
  cen + gamma • y

/-- The body on which the normalized recorded walk is actually executed. -/
abbrev normalizedBody (K : Set (State n)) (cen : State n) (gamma : Real) : Set (State n) :=
  chart cen gamma ⁻¹' K

theorem measurable_chart (cen : State n) (gamma : Real) :
    Measurable (chart cen gamma) := by
  unfold chart
  exact Ttc.measurable_inscribedAffine cen gamma

theorem measurableSet_normalizedBody {K : Set (State n)} (hK : MeasurableSet K)
    (cen : State n) (gamma : Real) :
    MeasurableSet (normalizedBody K cen gamma) :=
  hK.preimage (measurable_chart cen gamma)

/-- Operational membership bridge: the normalized oracle makes exactly the original-body
membership query at the affine image. -/
theorem mem_normalizedBody_iff {K : Set (State n)} (cen : State n) (gamma : Real)
    (y : State n) :
    y ∈ normalizedBody K cen gamma ↔ chart cen gamma y ∈ K :=
  Iff.rfl

/-- Map only the endpoint of the normalized recorded execution.  Its cost coordinate is
left untouched. -/
noncomputable def affineCostedBallWalkEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    (cen : State n) (gamma R M eps : Real)
    (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) : Measure (ENNReal × State n) :=
  Measure.map (fun z => (z.1, chart cen gamma z.2))
    (costedExplicitBallWalkEndpointLaw
      (measurableSet_normalizedBody hK cen gamma) R M eps hdelta mu)

theorem measurable_affineCostedEndpointMap (cen : State n) (gamma : Real) :
    Measurable (fun z : ENNReal × State n => (z.1, chart cen gamma z.2)) :=
  measurable_fst.prodMk ((measurable_chart cen gamma).comp measurable_snd)

instance isProbabilityMeasure_affineCostedBallWalkEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    (cen : State n) (gamma R M eps : Real)
    (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure
      (affineCostedBallWalkEndpointLaw hK cen gamma R M eps hdelta mu) := by
  unfold affineCostedBallWalkEndpointLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_affineCostedEndpointMap cen gamma).aemeasurable

/-- Forgetting recorded costs yields the normalized ball-walk endpoint, transported to the
original coordinates. -/
theorem map_snd_affineCostedBallWalkEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    (cen : State n) (gamma R M eps : Real)
    (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    Measure.map Prod.snd
        (affineCostedBallWalkEndpointLaw hK cen gamma R M eps hdelta mu) =
      Measure.map (chart cen gamma)
        (iterate
          (lazy (ballWalk (normalizedBody K cen gamma)
            (explicitBallWalkDelta n M eps))) mu
          (explicitBallWalkSteps n R M eps)) := by
  rw [affineCostedBallWalkEndpointLaw,
    Measure.map_map measurable_snd (measurable_affineCostedEndpointMap cen gamma)]
  change Measure.map (chart cen gamma ∘ Prod.snd)
      (costedExplicitBallWalkEndpointLaw
        (measurableSet_normalizedBody hK cen gamma) R M eps hdelta mu) = _
  rw [← Measure.map_map (measurable_chart cen gamma) measurable_snd]
  rw [map_snd_costedExplicitBallWalkEndpointLaw]

/-- Affine normalization changes no recorded membership-query cost. -/
theorem lintegral_fst_affineCostedBallWalkEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    (cen : State n) (gamma R M eps : Real)
    (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    (∫⁻ z, z.1 ∂affineCostedBallWalkEndpointLaw hK cen gamma R M eps hdelta mu) =
      (explicitBallWalkSteps n R M eps : ENNReal) * (2 : ENNReal)⁻¹ := by
  rw [affineCostedBallWalkEndpointLaw,
    lintegral_map measurable_fst (measurable_affineCostedEndpointMap cen gamma)]
  exact lintegral_fst_costedExplicitBallWalkEndpointLaw
    (measurableSet_normalizedBody hK cen gamma) R M eps hdelta mu

theorem map_uniformOn_chart {K : Set (State n)} (hK : MeasurableSet K)
    (cen : State n) {gamma : Real} (hgamma : 0 < gamma) :
    Measure.map (chart cen gamma)
        (Arlib.uniformOn volume (normalizedBody K cen gamma)) =
      Arlib.uniformOn volume K := by
  simpa only [chart, normalizedBody, add_comm] using
    (Arlib.MarkovChains.map_uniformOn_affineChart hgamma cen hK)

/-- The operational affine execution inherits the normalized mixing guarantee, with the
same TV error and exactly the same query count. -/
theorem tvLe_affineCostedBallWalkEndpointLaw [NeZero n]
    (hn : 2 ≤ n) {K : Set (State n)}
    (hK : MeasurableSet K) (hconv : Convex Real K)
    (cen : State n) {gamma : Real} (hgamma : 0 < gamma)
    (hball : ball cen gamma ⊆ K)
    {R M eps : Real} (hR : 0 < R)
    (hKR : ∀ x ∈ normalizedBody K cen gamma, ‖x‖ ≤ R)
    (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {mu : Measure (State n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm (ENNReal.ofReal M) mu
      (Arlib.uniformOn volume (normalizedBody K cen gamma))) :
    TVLe
      (Measure.map Prod.snd
        (affineCostedBallWalkEndpointLaw hK cen gamma R M eps
          (explicitBallWalkDelta_pos hn hM heps0) mu))
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  rw [map_snd_affineCostedBallWalkEndpointLaw, ← map_uniformOn_chart hK cen hgamma]
  exact Arlib.MarkovChains.tvLe_map (measurable_chart cen gamma)
    (tvLe_explicitBallWalk hn
      (measurableSet_normalizedBody hK cen gamma)
      (by simpa only [normalizedBody, chart, add_comm] using
        Ttc.convex_inscribedPreimage cen gamma hconv)
      (by simpa only [normalizedBody, chart, add_comm] using
        Ttc.ball_subset_inscribedPreimage hgamma hball)
      hR hKR hM heps0 heps1 hwarm)

/-! ## Inflated-polytope geometry -/

/-- Inflation's apparent aspect-ratio expression cancels exactly after normalization. -/
theorem inflated_normalized_radius_eq {gamma kappa D : Real}
    (hgamma : 0 < gamma) (hkappa : 0 ≤ kappa) :
    ((1 + kappa / gamma) * D) / (gamma + kappa) = D / gamma := by
  have hg0 : gamma ≠ 0 := ne_of_gt hgamma
  have hgk0 : gamma + kappa ≠ 0 := ne_of_gt (by linarith)
  field_simp

/-- A point of the normalized inflated body has norm at most the original diameter divided
by the original inradius.  Thus KV97 inflation does not worsen this radius parameter. -/
theorem norm_le_original_aspect_of_mem_normalized_inflated
    {I : Type*} {A : I → State n} {b : I → Real}
    {cp r : Real} (hcp : 0 ≤ cp)
    {cen : State n} {gamma D : Real} (hgamma : 0 < gamma)
    (hball : ball cen gamma ⊆ Arlib.Polytope.body A b)
    (hD : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b,
      dist x y ≤ D)
    {x : State n}
    (hx : x ∈ normalizedBody (Arlib.KV97.inflated A b cp r) cen
      (gamma + Arlib.KV97.kappaOf cp r)) :
    ‖x‖ ≤ D / gamma := by
  let kappa := Arlib.KV97.kappaOf cp r
  have hkappa : 0 ≤ kappa := Arlib.KV97.kappaOf_nonneg hcp
  have hrad : 0 < gamma + kappa := by linarith
  have hzero : (0 : State n) ∈
      normalizedBody (Arlib.KV97.inflated A b cp r) cen (gamma + kappa) := by
    have hunit : (0 : State n) ∈ ball 0 1 := Metric.mem_ball_self one_pos
    simpa only [normalizedBody, chart, add_comm] using
      (Ttc.ball_subset_inscribedPreimage hrad
        (Arlib.KV97.ball_subset_inflated hgamma hball) hunit)
  have hdist := Ttc.dist_le_of_mem_inscribedPreimage hrad
    (Arlib.KV97.dist_le_of_mem_inflated hgamma hcp hball hD) x hx 0 hzero
  have heq : ((1 + Arlib.KV97.kappaOf cp r / gamma) * D) /
      (gamma + kappa) = D / gamma :=
    inflated_normalized_radius_eq hgamma hkappa
  rw [heq] at hdist
  simpa only [dist_zero_right] using hdist

/-- The only geometry-derived warmness bound currently available for the normalized
inball start.  Its exponential dependence on `n` is explicit and intentional. -/
theorem isWarm_normalized_inball_pow
    {K : Set (State n)} (hK : MeasurableSet K)
    (cen : State n) {gamma D : Real} (hgamma : 0 < gamma)
    (hball : ball cen gamma ⊆ K)
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    IsWarm (ENNReal.ofReal ((D / gamma) ^ n))
      (Arlib.uniformOn volume (ball (0 : State n) 1))
      (Arlib.uniformOn volume (normalizedBody K cen gamma)) := by
  have hKm := measurableSet_normalizedBody hK cen gamma
  have hballNorm : ball (0 : State n) 1 ⊆ normalizedBody K cen gamma := by
    simpa only [normalizedBody, chart, add_comm] using
      Ttc.ball_subset_inscribedPreimage hgamma hball
  have hDnorm : ∀ x ∈ normalizedBody K cen gamma,
      ∀ y ∈ normalizedBody K cen gamma, dist x y ≤ D / gamma := by
    simpa only [normalizedBody, chart, add_comm] using
      Ttc.dist_le_of_mem_inscribedPreimage hgamma hD
  have hK0norm : volume (normalizedBody K cen gamma) ≠ 0 :=
    Arlib.MarkovChains.volume_ne_zero_of_ball_subset one_pos hballNorm
  have hKtopNorm : volume (normalizedBody K cen gamma) ≠ ⊤ :=
    Arlib.MarkovChains.volume_ne_top_of_diam_bound
      (hballNorm (Metric.mem_ball_self one_pos)) hDnorm
  simpa using Arlib.MarkovChains.isWarm_uniformOn_inscribed_pow
    hKm hK0norm hKtopNorm hDnorm one_pos hballNorm

/-- For the KV97 inflated body, the explicit normalized inball warmness factor is the
original aspect ratio to the dimension.  The inflation parameter cancels here as it did in
the radius bound. -/
theorem isWarm_normalized_inflated_inball_pow
    {I : Type*} {A : I → State n} {b : I → Real}
    {cp r : Real} (hcp : 0 ≤ cp)
    {cen : State n} {gamma D : Real} (hgamma : 0 < gamma)
    (hball : ball cen gamma ⊆ Arlib.Polytope.body A b)
    (hD : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b,
      dist x y ≤ D) :
    IsWarm (ENNReal.ofReal ((D / gamma) ^ n))
      (Arlib.uniformOn volume (ball (0 : State n) 1))
      (Arlib.uniformOn volume
        (normalizedBody (Arlib.KV97.inflated A b cp r) cen
          (gamma + Arlib.KV97.kappaOf cp r))) := by
  have hkappa : 0 ≤ Arlib.KV97.kappaOf cp r := Arlib.KV97.kappaOf_nonneg hcp
  have hrad : 0 < gamma + Arlib.KV97.kappaOf cp r := by linarith
  have hwarm := isWarm_normalized_inball_pow
    (Arlib.KV97.measurableSet_inflated A b cp r) cen hrad
    (Arlib.KV97.ball_subset_inflated hgamma hball)
    (Arlib.KV97.dist_le_of_mem_inflated hgamma hcp hball hD)
  rw [inflated_normalized_radius_eq hgamma hkappa] at hwarm
  exact hwarm

/-- Fully geometric specialization of the cost-preserving affine sampler to a KV97
inflated polytope.  The remaining scalar facts are displayed explicitly: positivity of the
original aspect ratio, and `1 ≤ (D/gamma)^n`.  No unidentified affine or membership-cost
binder remains. -/
theorem tvLe_affineCostedBallWalkEndpointLaw_inflated [NeZero n]
    (hn : 2 ≤ n)
    {I : Type*} {A : I → State n} {b : I → Real}
    {cp r : Real} (hcp : 0 ≤ cp)
    {cen : State n} {gamma D : Real} (hgamma : 0 < gamma)
    (hball : ball cen gamma ⊆ Arlib.Polytope.body A b)
    (hD : ∀ x ∈ Arlib.Polytope.body A b, ∀ y ∈ Arlib.Polytope.body A b,
      dist x y ≤ D)
    (hAspect : 0 < D / gamma) (hWarmOne : 1 ≤ (D / gamma) ^ n)
    {eps : Real} (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    TVLe
      (Measure.map Prod.snd
        (affineCostedBallWalkEndpointLaw
          (Arlib.KV97.measurableSet_inflated A b cp r) cen
          (gamma + Arlib.KV97.kappaOf cp r) (D / gamma) ((D / gamma) ^ n) eps
          (explicitBallWalkDelta_pos hn hWarmOne heps0)
          (Arlib.uniformOn volume (ball (0 : State n) 1))))
      (Arlib.uniformOn volume (Arlib.KV97.inflated A b cp r))
      (ENNReal.ofReal eps) := by
  let mu : Measure (State n) := Arlib.uniformOn volume (ball (0 : State n) 1)
  haveI : IsProbabilityMeasure mu := Arlib.isProbabilityMeasure_uniformOn volume
    (Metric.measure_ball_pos volume (0 : State n) one_pos).ne' measure_ball_lt_top.ne
  change TVLe
    (Measure.map Prod.snd
      (affineCostedBallWalkEndpointLaw
        (Arlib.KV97.measurableSet_inflated A b cp r) cen
        (gamma + Arlib.KV97.kappaOf cp r) (D / gamma) ((D / gamma) ^ n) eps
        (explicitBallWalkDelta_pos hn hWarmOne heps0) mu))
    (Arlib.uniformOn volume (Arlib.KV97.inflated A b cp r)) (ENNReal.ofReal eps)
  apply tvLe_affineCostedBallWalkEndpointLaw hn
    (Arlib.KV97.measurableSet_inflated A b cp r)
    (Arlib.KV97.convex_inflated A b cp r) cen
    (by have := Arlib.KV97.kappaOf_nonneg (r := r) hcp; linarith)
    (Arlib.KV97.ball_subset_inflated hgamma hball)
    hAspect
  · intro x hx
    exact norm_le_original_aspect_of_mem_normalized_inflated
      hcp hgamma hball hD hx
  · exact hWarmOne
  · exact heps0
  · exact heps1
  · exact isWarm_normalized_inflated_inball_pow hcp hgamma hball hD

#print axioms tvLe_affineCostedBallWalkEndpointLaw
#print axioms lintegral_fst_affineCostedBallWalkEndpointLaw
#print axioms norm_le_original_aspect_of_mem_normalized_inflated
#print axioms isWarm_normalized_inball_pow
#print axioms tvLe_affineCostedBallWalkEndpointLaw_inflated

end Ttc.AffinePolynomialBallWalkKV97Sampler
