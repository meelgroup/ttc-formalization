/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.MarkovChains.Continuous.BallWalkWarmLSAdapter
import Arlib.MarkovChains.Continuous.SpeedyToUniform
import Ttc.Exec.RawBallWalkQueryCost
import Ttc.Exec.KV97RoundedEndpointBridge

/-!
# An explicit warm ball-walk execution for the KV97 rounding sampler

This file chooses all scalar parameters left by `BallWalkWarmLSAdapter`.  For a convex
body containing the unit ball and contained in the radius-`R` ball, it uses

* `delta = eps / (4 M n)`;
* the explicit geometric lower bound exported by `BallWalkTransfer`, divided by two;
* the natural ceiling of the resulting Lovasz--Simonovits deadline.

The corresponding recorded execution performs exactly `steps / 2` expected body-membership
queries.  After KV97 randomized rounding and rejection, the expected actual query count is
at most eight times `steps / 2 + 1`, under the repository's proved `1/8` acceptance
certificate.  No unit-cost draw or hidden sampling oracle is introduced.

The claim here is deliberately parameterized: the displayed deadline is polynomial in the
numeric parameters `n`, `R`, `M`, and `1/eps` up to its logarithm.  This file does not claim
that a particular TTC input has polynomially bounded `R` or `M`.  Instantiating an arbitrary
inflated polytope also still requires the standard affine normalization taking its inscribed
ball to the unit ball; no cost-preserving affine execution theorem is assumed here.
-/

namespace Ttc.PolynomialBallWalkKV97Sampler

open MeasureTheory ProbabilityTheory Metric Set Function
open Arlib Arlib.MarkovChains
open Ttc.RawBallWalkQueryCost
open Ttc.KV97RoundedEndpointBridge
open Ttc.CostedKV97Rounding
open scoped ENNReal Classical

variable {n : Nat}

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Polynomially small ordinary ball-walk radius. -/
noncomputable def explicitBallWalkDelta (n : Nat) (M eps : Real) : Real :=
  eps / (4 * M * (n : Real))

/-- The exact real conductance scalar supplied by the geometric lower bound in
`BallWalkWarmLSAdapter`. -/
noncomputable def explicitBallWalkPhi (n : Nat) (R M eps : Real) : Real :=
  (min (1 / 16 : ENNReal)
      (ENNReal.ofReal (1 / (8 * R)) *
        ENNReal.ofReal (explicitBallWalkDelta n M eps / (2 * (n : Real))) / 64) / 2).toReal

/-- Explicit natural deadline.  The `max 0` totalizes the definition; under the sampler
hypotheses the ordinary LS threshold is nonnegative. -/
noncomputable def explicitBallWalkSteps (n : Nat) (R M eps : Real) : Nat :=
  ⌈max 0 (lsThresholdS M (explicitBallWalkPhi n R M eps) eps)⌉₊

theorem explicitBallWalkDelta_pos (hn : 2 ≤ n) {M eps : Real}
    (hM : 1 ≤ M) (heps0 : 0 < eps) :
    0 < explicitBallWalkDelta n M eps := by
  unfold explicitBallWalkDelta
  positivity

theorem explicitBallWalkDelta_lt_one (hn : 2 ≤ n) {M eps : Real}
    (hM : 1 ≤ M) (heps1 : eps ≤ 1) :
    explicitBallWalkDelta n M eps < 1 := by
  have hnR : (2 : Real) ≤ (n : Real) := by exact_mod_cast hn
  unfold explicitBallWalkDelta
  have hden : (0 : Real) < 4 * M * (n : Real) := by positivity
  apply (div_lt_one hden).2
  nlinarith

theorem explicitBallWalk_smooth (hn : 2 ≤ n) {M eps : Real}
    (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    1 - ENNReal.ofReal ((1 - explicitBallWalkDelta n M eps) ^ n) ≤
      ENNReal.ofReal (eps / (2 * M)) := by
  let delta := explicitBallWalkDelta n M eps
  have hdelta0 : 0 < delta := explicitBallWalkDelta_pos hn hM heps0
  have hdelta1 : delta < 1 := explicitBallWalkDelta_lt_one hn hM heps1
  have hber : 1 - (n : Real) * delta ≤ (1 - delta) ^ n :=
    one_sub_nsmul_le_pow_one_sub hdelta1.le n
  have hpow0 : 0 ≤ (1 - delta) ^ n := pow_nonneg (by linarith) n
  have hpow1 : (1 - delta) ^ n ≤ 1 := by
    exact pow_le_one₀ (by linarith) (by linarith)
  have hn0 : (n : Real) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hM0 : M ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hM)
  have hndelta : (n : Real) * delta = eps / (4 * M) := by
    unfold delta explicitBallWalkDelta
    field_simp
  have hreal : 1 - (1 - delta) ^ n ≤ eps / (2 * M) := by
    calc
      1 - (1 - delta) ^ n ≤ (n : Real) * delta := by linarith
      _ = eps / (4 * M) := hndelta
      _ ≤ eps / (2 * M) := by
        have hMpos : 0 < M := lt_of_lt_of_le one_pos hM
        exact div_le_div_of_nonneg_left heps0.le (by positivity) (by nlinarith)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hpow0]
  exact ENNReal.ofReal_le_ofReal hreal

theorem explicitBallWalkPhi_pos (hn : 2 ≤ n) {R M eps : Real}
    (hR : 0 < R) (hM : 1 ≤ M) (heps0 : 0 < eps) :
    0 < explicitBallWalkPhi n R M eps := by
  unfold explicitBallWalkPhi
  apply ENNReal.toReal_pos
  · apply ENNReal.div_ne_zero.2
    constructor
    · apply ne_of_gt
      apply lt_min
      · norm_num
      · apply ENNReal.div_pos
        · exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
            (ENNReal.ofReal_ne_zero_iff.mpr (by
              have := explicitBallWalkDelta_pos hn hM heps0
              positivity))
        · norm_num
    · norm_num
  · apply ENNReal.div_ne_top
    · exact ne_top_of_le_ne_top (by finiteness : (1 / 16 : ENNReal) ≠ ⊤)
        (min_le_left _ _)
    · norm_num

theorem explicitBallWalkPhi_le_half (n : Nat) (R M eps : Real) :
    explicitBallWalkPhi n R M eps ≤ 1 / 2 := by
  unfold explicitBallWalkPhi
  have hle : min (1 / 16 : ENNReal)
      (ENNReal.ofReal (1 / (8 * R)) *
        ENNReal.ofReal (explicitBallWalkDelta n M eps / (2 * (n : Real))) / 64) / 2 ≤
      1 / 2 := by
    calc
      _ ≤ (1 / 16 : ENNReal) / 2 := by gcongr; exact min_le_left _ _
      _ ≤ 1 / 2 := by
        rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        simp only [ENNReal.div_eq_inv_mul, mul_one]
        rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
        simpa using (ENNReal.inv_le_inv.mpr (by norm_num : (1 : ENNReal) ≤ 16))
  have hreal := ENNReal.toReal_mono (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hle
  simpa [ENNReal.toReal_div] using hreal

theorem ofReal_explicitBallWalkPhi (n : Nat) (R M eps : Real) :
    ENNReal.ofReal (explicitBallWalkPhi n R M eps) =
      min (1 / 16)
        (ENNReal.ofReal (1 / (8 * R)) *
          ENNReal.ofReal (explicitBallWalkDelta n M eps / (2 * (n : Real))) / 64) / 2 := by
  unfold explicitBallWalkPhi
  apply ENNReal.ofReal_toReal
  apply ENNReal.div_ne_top
  · exact ne_top_of_le_ne_top (by finiteness : (1 / 16 : ENNReal) ≠ ⊤)
      (min_le_left _ _)
  · norm_num

theorem lsThreshold_le_explicitBallWalkSteps (n : Nat) (R M eps : Real) :
    lsThresholdS M (explicitBallWalkPhi n R M eps) eps ≤
      (explicitBallWalkSteps n R M eps : Real) := by
  exact (le_max_right 0 _).trans (Nat.le_ceil _)

/-- Explicit polynomial-parameter warm mixing theorem for the ordinary lazy ball walk. -/
theorem tvLe_explicitBallWalk [NeZero n]
    (hn : 2 ≤ n) {K : Set (State n)}
    (hK : MeasurableSet K) (hconv : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {R M eps : Real} (hR : 0 < R)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {mu : Measure (State n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm (ENNReal.ofReal M) mu (Arlib.uniformOn volume K)) :
    TVLe (iterate (lazy (ballWalk K (explicitBallWalkDelta n M eps))) mu
        (explicitBallWalkSteps n R M eps))
      (Arlib.uniformOn volume K) (ENNReal.ofReal eps) := by
  apply tvLe_iterate_lazy_ballWalk_warm_of_geometry hn hK hconv hball hR hKR
    (explicitBallWalkDelta_pos hn hM heps0)
    (explicitBallWalkDelta_lt_one hn hM heps1) hM
    (explicitBallWalkPhi_pos hn hR hM heps0)
    (explicitBallWalkPhi_le_half n R M eps) heps0 heps1 hwarm
    (explicitBallWalk_smooth hn hM heps0 heps1)
  · rw [ofReal_explicitBallWalkPhi]
  · exact lsThreshold_le_explicitBallWalkSteps n R M eps

/-- Recorded actual-query endpoint law of the explicit lazy ball-walk execution. -/
noncomputable def costedExplicitBallWalkEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    (R M eps : Real) (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) : Measure (ENNReal × State n) :=
  Measure.map
    (fun omega =>
      (Ttc.SequentialCost.totalCost (explicitBallWalkSteps n R M eps) omega,
        (omega (explicitBallWalkSteps n R M eps)).2))
    (Ttc.RawGaussianQueryCost.lazyRawQueryExecution hK
      (explicitBallWalkDelta n M eps) 0 hdelta mu)

theorem measurable_costedExplicitBallWalkEndpointMap (n : Nat) (R M eps : Real) :
    Measurable (fun omega : Nat -> ENNReal × State n =>
      (Ttc.SequentialCost.totalCost (explicitBallWalkSteps n R M eps) omega,
        (omega (explicitBallWalkSteps n R M eps)).2)) :=
  (Ttc.SequentialCost.measurable_totalCost _).prodMk
    (measurable_snd.comp (measurable_pi_apply _))

theorem map_snd_costedExplicitBallWalkEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    (R M eps : Real) (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    Measure.map Prod.snd
        (costedExplicitBallWalkEndpointLaw hK R M eps hdelta mu) =
      iterate (lazy (ballWalk K (explicitBallWalkDelta n M eps))) mu
        (explicitBallWalkSteps n R M eps) := by
  rw [costedExplicitBallWalkEndpointLaw,
    Measure.map_map measurable_snd (measurable_costedExplicitBallWalkEndpointMap n R M eps)]
  exact map_lazyRawQueryExecution_output_eq_ballWalk hK
    (explicitBallWalkDelta n M eps) hdelta mu (explicitBallWalkSteps n R M eps)

theorem lintegral_fst_costedExplicitBallWalkEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    (R M eps : Real) (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    (∫⁻ z, z.1 ∂costedExplicitBallWalkEndpointLaw hK R M eps hdelta mu) =
      (explicitBallWalkSteps n R M eps : ENNReal) * (2 : ENNReal)⁻¹ := by
  rw [costedExplicitBallWalkEndpointLaw, lintegral_map measurable_fst
    (measurable_costedExplicitBallWalkEndpointMap n R M eps)]
  exact lintegral_lazyBallWalkQueryCost hK
    (explicitBallWalkDelta n M eps) hdelta mu (explicitBallWalkSteps n R M eps)

instance isProbabilityMeasure_costedExplicitBallWalkEndpointLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    (R M eps : Real) (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (costedExplicitBallWalkEndpointLaw hK R M eps hdelta mu) := by
  unfold costedExplicitBallWalkEndpointLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_costedExplicitBallWalkEndpointMap n R M eps).aemeasurable

section RoundedSampler

variable {A : Type*} {D : DNF A}

/-- Complete recorded-query law: explicit lazy ball-walk endpoint, one randomized-rounding
membership query per attempt, and iid rejection until the rounded point is accepted. -/
noncomputable def costedExplicitKV97SamplerLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    (R M eps : Real) (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) (body : A -> Set (State n))
    (rho : Int) (i : Cube A) : Measure (ENNReal × State n) :=
  costedFineEndpointLaw
    (costedExplicitBallWalkEndpointLaw hK R M eps hdelta mu) body rho i

/-- State marginal of the complete operational sampler. -/
theorem map_snd_costedExplicitKV97SamplerLaw
    {K : Set (State n)} (hK : MeasurableSet K)
    (R M eps : Real) (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) [IsProbabilityMeasure mu]
    (body : A -> Set (State n)) (rho : Int) (i : Cube A)
    (hpos : 0 < roundedMeasure
      (iterate (lazy (ballWalk K (explicitBallWalkDelta n M eps))) mu
        (explicitBallWalkSteps n R M eps))
      (integerAcceptance body rho i)) :
    Measure.map Prod.snd
        (costedExplicitKV97SamplerLaw hK R M eps hdelta mu body rho i) =
      conditionedFineEndpointLaw
        (iterate (lazy (ballWalk K (explicitBallWalkDelta n M eps))) mu
          (explicitBallWalkSteps n R M eps)) body rho i := by
  unfold costedExplicitKV97SamplerLaw
  have hm := map_snd_costedExplicitBallWalkEndpointLaw hK R M eps hdelta mu
  rw [← hm]
  exact map_snd_costedFineEndpointLaw _ body rho i (by rw [hm]; exact hpos)

/-- Expected actual membership queries of the complete sampler under a supplied acceptance
lower bound.  With `acceptLower = 1/8`, this is exactly the promised eightfold rejection
overhead on `steps/2 + 1`. -/
theorem lintegral_fst_costedExplicitKV97SamplerLaw_le
    {K : Set (State n)} (hK : MeasurableSet K)
    (R M eps : Real) (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) [IsProbabilityMeasure mu]
    (body : A -> Set (State n)) (rho : Int) (i : Cube A)
    {acceptLower : ENNReal}
    (haccept : acceptLower ≤ roundedMeasure
      (iterate (lazy (ballWalk K (explicitBallWalkDelta n M eps))) mu
        (explicitBallWalkSteps n R M eps))
      (integerAcceptance body rho i)) :
    (∫⁻ z, z.1 ∂costedExplicitKV97SamplerLaw hK R M eps hdelta mu body rho i) ≤
      acceptLower⁻¹ *
        ((explicitBallWalkSteps n R M eps : ENNReal) * (2 : ENNReal)⁻¹ + 1) := by
  unfold costedExplicitKV97SamplerLaw
  apply lintegral_fst_costedFineEndpointLaw_le
  · simpa [map_snd_costedExplicitBallWalkEndpointLaw] using haccept
  · exact le_of_eq (lintegral_fst_costedExplicitBallWalkEndpointLaw
      hK R M eps hdelta mu)

/-- Concrete KV97 `1/8` cost corollary.  The acceptance premise is exactly what
`one_eighth_le_roundedMeasure_integerAcceptance_of_kv97` proves from the repository's
inflated-polytope geometry and Theorem-2 hypotheses. -/
theorem lintegral_fst_costedExplicitKV97SamplerLaw_le_eighth
    {K : Set (State n)} (hK : MeasurableSet K)
    (R M eps : Real) (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) [IsProbabilityMeasure mu]
    (body : A -> Set (State n)) (rho : Int) (i : Cube A)
    (haccept : ENNReal.ofReal ((1 : Real) / 8) ≤ roundedMeasure
      (iterate (lazy (ballWalk K (explicitBallWalkDelta n M eps))) mu
        (explicitBallWalkSteps n R M eps))
      (integerAcceptance body rho i)) :
    (∫⁻ z, z.1 ∂costedExplicitKV97SamplerLaw hK R M eps hdelta mu body rho i) ≤
      (ENNReal.ofReal ((1 : Real) / 8))⁻¹ *
        ((explicitBallWalkSteps n R M eps : ENNReal) * (2 : ENNReal)⁻¹ + 1) :=
  lintegral_fst_costedExplicitKV97SamplerLaw_le
    hK R M eps hdelta mu body rho i haccept

/-- Package the explicit execution against the exact `kv97SampD` measure realization. -/
noncomputable def explicitExpectedQueryKV97Sampler
    {K : Set (State n)} (hK : MeasurableSet K)
    (R M eps : Real) (hdelta : 0 < explicitBallWalkDelta n M eps)
    (mu : Measure (State n)) [IsProbabilityMeasure mu]
    (body : A -> Set (State n)) (rho : Int)
    (law : {c : Cube A // c ∈ D} -> Measure (State n))
    (i : {c : Cube A // c ∈ D})
    (hmarg : iterate (lazy (ballWalk K (explicitBallWalkDelta n M eps))) mu
      (explicitBallWalkSteps n R M eps) = law i)
    (hpos : 0 < roundedMeasure (law i) (integerAcceptance body rho i.val)) :
    ExpectedQueryFineSampler (kv97SampMeasure body rho law i) :=
  expectedQueryKV97Sampler
    (costedExplicitBallWalkEndpointLaw hK R M eps hdelta mu) body rho law i
      ((map_snd_costedExplicitBallWalkEndpointLaw hK R M eps hdelta mu).trans hmarg) hpos

end RoundedSampler

#print axioms tvLe_explicitBallWalk
#print axioms map_snd_costedExplicitBallWalkEndpointLaw
#print axioms lintegral_fst_costedExplicitBallWalkEndpointLaw
#print axioms lintegral_fst_costedExplicitKV97SamplerLaw_le_eighth
#print axioms explicitExpectedQueryKV97Sampler

end Ttc.PolynomialBallWalkKV97Sampler
