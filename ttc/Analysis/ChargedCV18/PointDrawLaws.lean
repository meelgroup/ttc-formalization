/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18
import ttc.Analysis.ChargedCV18.GaussianSampling
import ttc.Analysis.ChargedCV18.Program

/-!
# The point draws from random numbers

`cv18Program` builds its two kinds of random point from random numbers:

* a ball-walk proposal around `x` of radius `r` is `x + r · (u^{1/n} / ‖g‖) · g`, for a
  standard Gaussian vector `g` and a uniform `u ∈ [0, 1]`;
* the starting point is `√σ₀² · g` for a standard Gaussian vector `g`.

This file proves that these have the laws the accuracy proof uses: `uniformBall n x r`
(`uniformBall_eq_map`) and `initialGaussianLaw q` (`initialGaussianLaw_eq_map`).
-/

open MeasureTheory ProbabilityTheory Metric Set
open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory
open scoped ENNReal

namespace ttc.ChargedCV18

open ArlibCommunity.Algorithms.CV18

/-- Two probability measures that are multiples of the same measure are equal. -/
theorem eq_of_smul_of_isProbabilityMeasure {X : Type*} [MeasurableSpace X]
    {μ ν m : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℝ≥0∞)
    (hμ : μ = a • m) (hν : ν = b • m) : μ = ν := by
  have h1 : a * m univ = 1 := by
    rw [← measure_univ (μ := μ), hμ, Measure.smul_apply, smul_eq_mul]
  have h2 : b * m univ = 1 := by
    rw [← measure_univ (μ := ν), hν, Measure.smul_apply, smul_eq_mul]
  have hm0 : m univ ≠ 0 := fun h => by simp [h] at h1
  have hmtop : m univ ≠ ⊤ := fun h => by
    rw [h] at h1
    rcases eq_or_ne a 0 with ha | ha
    · simp [ha] at h1
    · simp [ENNReal.mul_top ha] at h1
  have hab : a = b := by
    have := h1.trans h2.symm
    exact (ENNReal.mul_left_inj hm0 hmtop).mp this
  rw [hμ, hν, hab]

theorem uniformUnit_eq : uniformUnit = volume.restrict (Icc (0 : ℝ) 1) := by
  have hprob : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  refine eq_of_smul_of_isProbabilityMeasure (uniformUnitFinite.mass : ℝ≥0∞)⁻¹ 1 ?_ (one_smul _ _).symm
  have hne : uniformUnitFinite ≠ 0 := by
    intro h
    have : (uniformUnitFinite : Measure ℝ) univ = 0 := by rw [h]; rfl
    change volume.restrict (Icc (0 : ℝ) 1) univ = 0 at this
    simp at this
  unfold uniformUnit
  rw [uniformUnitFinite.toMeasure_normalize_eq_of_nonzero hne, ← Measure.coe_nnreal_smul,
    ENNReal.coe_inv (uniformUnitFinite.mass_nonzero_iff.mpr hne)]
  rfl

/-- A uniform point of the ball of radius `r > 0` is the unit-ball point scaled by `r`. -/
theorem uniformOn_ball_eq_map_smul {n : ℕ} [NeZero n] {r : ℝ} (hr : 0 < r) :
    uniformOn volume (ball (0 : AmbientSpace n) r) =
      (uniformOn volume (ball (0 : AmbientSpace n) 1)).map (r • ·) := by
  have hball : ∀ s : ℝ, 0 < s → volume (ball (0 : AmbientSpace n) s) ≠ 0 := fun s hs =>
    (measure_ball_pos volume _ hs).ne'
  have hfin : ∀ s : ℝ, volume (ball (0 : AmbientSpace n) s) ≠ ⊤ := fun s =>
    measure_ball_lt_top.ne
  have : IsProbabilityMeasure (uniformOn volume (ball (0 : AmbientSpace n) r)) :=
    isProbabilityMeasure_uniformOn _ (hball r hr) (hfin r)
  have : IsProbabilityMeasure (uniformOn volume (ball (0 : AmbientSpace n) 1)) :=
    isProbabilityMeasure_uniformOn _ (hball 1 one_pos) (hfin 1)
  let e := MeasurableEquiv.smul₀ (α := AmbientSpace n) r hr.ne'
  have hpre : e ⁻¹' ball (0 : AmbientSpace n) r = ball 0 1 := by
    ext y
    have he : e y = r • y := rfl
    simp only [mem_preimage, mem_ball, dist_zero_right, he, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
    constructor
    · intro h; nlinarith [norm_nonneg y]
    · intro h; nlinarith [norm_nonneg y]
  have hmap : (volume.restrict (ball (0 : AmbientSpace n) 1)).map (r • ·) =
      ENNReal.ofReal (abs (r ^ Module.finrank ℝ (AmbientSpace n))⁻¹) •
        volume.restrict (ball (0 : AmbientSpace n) r) := by
    change (volume.restrict (ball (0 : AmbientSpace n) 1)).map e = _
    rw [← hpre, ← MeasurableEquiv.restrict_map]
    change (volume.map (r • ·)).restrict _ = _
    rw [Measure.map_addHaar_smul volume hr.ne', Measure.restrict_smul]
  refine eq_of_smul_of_isProbabilityMeasure (volume (ball (0 : AmbientSpace n) r))⁻¹
    ((volume (ball (0 : AmbientSpace n) 1))⁻¹ *
      ENNReal.ofReal (abs (r ^ Module.finrank ℝ (AmbientSpace n))⁻¹))
    (uniformOn_def _ _) ?_
  rw [uniformOn_def, Measure.map_smul, hmap, smul_smul]
  fun_prop

/-- **The ball-walk proposal law.** For `r > 0`, a uniform point of the ball of radius `r`
around `x` is `x + r · ballStartMap n (g, u)` for `g` standard Gaussian and `u` uniform on
`[0, 1]`. -/
theorem uniformBall_eq_map {n : ℕ} [NeZero n] (x : AmbientSpace n) {r : ℝ} (hr : 0 < r) :
    uniformBall n x r =
      ((standardGaussian n).prod uniformUnit).map
        fun ω => x + r • GaussianSampling.ballStartMap n ω := by
  have hbs : Measurable (GaussianSampling.ballStartMap n) :=
    GaussianSampling.measurable_ballStartMap
  rw [uniformBall, centeredBall_eq_openBall hr, ← uniformOn_def, uniformOn_ball_eq_map_smul hr,
    ← GaussianSampling.ballStartMap_law, uniformUnit_eq, standardGaussian,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) hbs]
  rfl

/-- The standard Gaussian has density `(2π)^{-n/2} e^{-‖x‖²/2}`. -/
theorem standardGaussian_eq_withDensity (n : ℕ) :
    standardGaussian n =
      volume.withDensity fun y => GaussianSampling.radialDensity n ‖y‖ := by
  ext A hA
  rw [standardGaussian, GaussianSampling.stdGaussian_apply n hA, withDensity_apply _ hA]

/-- **The starting-point law.** `initialGaussianLaw q` is the law of `√σ₀² · g` for `g` a
standard Gaussian vector. -/
theorem initialGaussianLaw_eq_map (q : VolumeParams) :
    initialGaussianLaw q =
      (standardGaussian q.n).map (Real.sqrt (initialVariance q) • ·) := by
  set v := initialVariance q
  have hv : 0 < v := initialVariance_pos q
  set s := Real.sqrt v
  have hs : 0 < s := Real.sqrt_pos.mpr hv
  have hn : 0 < q.n := lt_of_lt_of_le (by norm_num) q.dim_ok
  have : NeZero q.n := ⟨hn.ne'⟩
  let m : Measure (AmbientSpace q.n) :=
    volume.withDensity fun x => ENNReal.ofReal (gaussianDensity v x)
  have hZ := initialGaussianIntegral_pos q
  -- the target is a multiple of `m`
  have hlaw : initialGaussianLaw q = ENNReal.ofReal (initialGaussianIntegral q)⁻¹ • m := by
    unfold initialGaussianLaw
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext x
    rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hZ.le), div_eq_mul_inv,
      mul_comm]
  -- the scaled Gaussian is a multiple of `m`
  let e := MeasurableEquiv.smul₀ (α := AmbientSpace q.n) s hs.ne'
  let c : ℝ≥0∞ := ENNReal.ofReal (abs (s ^ Module.finrank ℝ (AmbientSpace q.n))⁻¹)
  have hvol : volume.map e = c • (volume : Measure (AmbientSpace q.n)) :=
    Measure.map_addHaar_smul volume hs.ne'
  have hdens : ∀ x : AmbientSpace q.n,
      GaussianSampling.radialDensity q.n ‖e.symm x‖ =
        ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ q.n) * ENNReal.ofReal (gaussianDensity v x) := by
    intro x
    rw [GaussianSampling.radialDensity, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hsymm : e.symm x = s⁻¹ • x := rfl
    rw [hsymm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, gaussianDensity]
    congr 2
    rw [mul_pow, inv_pow, Real.sq_sqrt hv.le]
    field_simp
  have hgauss : (standardGaussian q.n).map (s • ·) =
      (c * ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ q.n)) • m := by
    ext A hA
    change (standardGaussian q.n).map e A = _
    rw [Measure.map_apply e.measurable hA, standardGaussian_eq_withDensity,
      withDensity_apply _ (e.measurable hA), Measure.smul_apply, smul_eq_mul,
      withDensity_apply _ hA]
    have hcomp : (fun y : AmbientSpace q.n => GaussianSampling.radialDensity q.n ‖y‖) =
        (fun x => GaussianSampling.radialDensity q.n ‖e.symm x‖) ∘ e := by
      funext y; simp
    rw [hcomp, ← lintegral_indicator (e.measurable hA)]
    rw [show (e ⁻¹' A).indicator ((fun x => GaussianSampling.radialDensity q.n ‖e.symm x‖) ∘ e)
        = (A.indicator fun x => GaussianSampling.radialDensity q.n ‖e.symm x‖) ∘ e by
      funext y
      by_cases h : e y ∈ A <;> simp [h]]
    simp only [Function.comp_def]
    rw [← lintegral_map_equiv (fun x => A.indicator
      (fun x => GaussianSampling.radialDensity q.n ‖e.symm x‖) x) e, hvol, lintegral_smul_measure, lintegral_indicator hA]
    simp_rw [hdens]
    rw [lintegral_const_mul _ (by unfold gaussianDensity; fun_prop), mul_assoc]
    rfl
  exact eq_of_smul_of_isProbabilityMeasure _ _ hlaw hgauss

end ttc.ChargedCV18
