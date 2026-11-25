/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.JacobianOneDim
import ArlibCommunity.Foundations.MarkovChainTheory.HitAndRunMixing.Model.Prelude
import ArlibCommunity.Foundations.Convex.Basic.UniformOn

/-!
# Sampling from Gaussian vectors and uniform numbers

Two facts that let an algorithm draw its random points from independent standard
Gaussians and uniform numbers, the random numbers a real-RAM machine reads:

* `stdGaussian_apply`: the standard Gaussian on `ℝⁿ` has density
  `(2π)^{-n/2} e^{-‖x‖²/2}`;
* `stdGaussian_map_direction`: a normalized standard Gaussian vector `g / ‖g‖` is uniform
  on the unit sphere;
* `ballStartMap_law`: for `g` standard Gaussian and `u` uniform on `[0, 1]`,
  `(u^{1/n} / ‖g‖) · g` is uniform on the unit ball.

The direction is uniform because the Gaussian density depends only on the norm, so in
polar coordinates its direction has a law proportional to the sphere's surface measure.
The radius `u^{1/n}` has density `n r^{n−1}` on `(0, 1)` (a change of variables `u = r^n`),
and in polar coordinates the uniform law on the ball is the product of the two.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace ttc.ChargedCV18.GaussianSampling

open ArlibCommunity.Foundations.MarkovChainTheory

/-- Tonelli for a product of one-variable functions on `ℝⁿ`. -/
theorem lintegral_pi_prod : ∀ (n : ℕ) (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞), (∀ i, Measurable (f i)) →
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, f i t ∂μ i
  | 0, μ, _, f, _ => by simp
  | n + 1, μ, _, f, hf => by
      have hmp := measurePreserving_piFinSuccAbove μ 0
      rw [← hmp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp only [Fin.prod_univ_succ]
      have hsplit : ∀ p : ℝ × (Fin n → ℝ),
          f 0 (((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm p) 0) *
            ∏ i : Fin n, f i.succ (((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm p)
              i.succ) =
          f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i) := by
        intro p
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
      simp_rw [hsplit]
      rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → ℝ => ∏ i, f i.succ (y i))
        (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable]
      rw [lintegral_pi_prod n (fun j => μ (Fin.succAbove 0 j)) (fun i => f i.succ)
        (fun i => hf i.succ)]
      simp

/-- Independent standard Gaussians in each coordinate have the product density. -/
theorem pi_gaussianReal_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi,
    lintegral_pi_prod n _ _ (fun _ => measurable_gaussianPDF 0 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ (hs i)]

/-- The standard Gaussian density on `ℝⁿ`, as a function of the norm:
`φ(r) = (2π)^{-n/2} e^{-r²/2}`. -/
noncomputable def radialDensity (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ n * Real.exp (-r ^ 2 / 2))

theorem measurable_radialDensity (n : ℕ) : Measurable (radialDensity n) := by
  unfold radialDensity; fun_prop

theorem prod_gaussianPDF_eq (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    ∏ i, gaussianPDF 0 1 (y i) = radialDensity n ‖y‖ := by
  rw [radialDensity, gaussianPDF_def,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 _)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    EuclideanSpace.real_norm_sq_eq, Finset.sum_neg_distrib, Finset.sum_div, neg_div]

/-- **The standard Gaussian has density `φ(‖x‖)`.** -/
theorem stdGaussian_apply (n : ℕ) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : MeasurableSet A) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) A = ∫⁻ y in A, radialDensity n ‖y‖ := by
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) hA,
    pi_gaussianReal_eq_withDensity, withDensity_apply _ (by measurability)]
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin n)).setLIntegral_comp_preimage_emb hemb]
  refine setLIntegral_congr_fun (hemb.measurable hA) fun x _ => ?_
  rw [← prod_gaussianPDF_eq]

/-! ## The direction `g / ‖g‖` -/

variable {n : ℕ} [NeZero n]

/-- `g / ‖g‖` as a point of `ℝⁿ`, with an arbitrary unit vector at `g = 0` (a null event). -/
noncomputable def directionVal (n : ℕ) [NeZero n] (g : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  if g = 0 then EuclideanSpace.single 0 1 else ‖g‖⁻¹ • g

theorem directionVal_mem (g : EuclideanSpace ℝ (Fin n)) :
    directionVal n g ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  unfold directionVal
  split_ifs with h
  · simp
  · simp [norm_smul, h]

/-- The direction `g / ‖g‖` of a vector, on the unit sphere. -/
noncomputable def direction (n : ℕ) [NeZero n] (g : EuclideanSpace ℝ (Fin n)) :
    sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨directionVal n g, directionVal_mem g⟩

theorem measurable_direction : Measurable (direction n) := by
  refine Measurable.subtype_mk ?_
  unfold directionVal
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

theorem direction_eq_polar (y : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) :
    direction n y = (homeomorphUnitSphereProd _ y).1 := by
  have hy : (y : EuclideanSpace ℝ (Fin n)) ≠ 0 := y.2
  apply Subtype.ext
  simp [direction, directionVal, hy]

/-- The radial mass of the Gaussian density in polar coordinates. -/
noncomputable def radialMass (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ r, radialDensity n r.1
    ∂Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)

/-- **Polar coordinates.** The Gaussian mass of the cone over `s` is `toSphere s` times the
radial mass. -/
theorem stdGaussian_direction_preimage {s : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)}
    (hs : MeasurableSet s) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) (direction n ⁻¹' s) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere s * radialMass n := by
  have hD : MeasurableSet (direction n ⁻¹' s) := measurable_direction hs
  have h0 : MeasurableSet ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    (measurableSet_singleton 0).compl
  rw [stdGaussian_apply n hD, ← lintegral_indicator hD]
  conv_lhs => rw [← restrict_compl_singleton (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) 0,
    ← lintegral_subtype_comap h0]
  have hpt : ∀ y : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
      (direction n ⁻¹' s).indicator (fun y => radialDensity n ‖y‖) (y : EuclideanSpace ℝ (Fin n)) =
        (fun p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Ioi (0 : ℝ) =>
          s.indicator 1 p.1 * radialDensity n p.2.1) (homeomorphUnitSphereProd _ y) := by
    intro y
    have hnorm : ‖(y : EuclideanSpace ℝ (Fin n))‖ = ((homeomorphUnitSphereProd _ y).2 : ℝ) := by
      simp
    dsimp only
    by_cases hy : direction n y ∈ s
    · have hy' : (homeomorphUnitSphereProd _ y).1 ∈ s := direction_eq_polar y ▸ hy
      rw [Set.indicator_of_mem (show (y : EuclideanSpace ℝ (Fin n)) ∈ direction n ⁻¹' s from hy),
        Set.indicator_of_mem hy', hnorm, Pi.one_apply, one_mul]
    · have hy' : (homeomorphUnitSphereProd _ y).1 ∉ s := direction_eq_polar y ▸ hy
      rw [Set.indicator_of_notMem (show (y : EuclideanSpace ℝ (Fin n)) ∉ direction n ⁻¹' s from hy),
        Set.indicator_of_notMem hy', zero_mul]
  refine (lintegral_congr hpt).trans ?_
  refine ((Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℝ (Fin n)))).lintegral_comp_emb
      (Homeomorph.measurableEmbedding _)
      (fun p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Ioi (0 : ℝ) =>
        s.indicator 1 p.1 * radialDensity n p.2.1)).trans ?_
  rw [lintegral_prod_mul (f := s.indicator 1) (g := fun r : Ioi (0 : ℝ) => radialDensity n r.1)
    (aemeasurable_const.indicator hs)
    ((measurable_radialDensity n).comp measurable_subtype_coe).aemeasurable,
    lintegral_indicator_one hs]
  rfl

/-- **A normalized standard Gaussian vector is uniform on the sphere.** -/
theorem stdGaussian_map_direction :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map (direction n) =
      ArlibCommunity.Foundations.MarkovChainTheory.unifSphere n := by
  set T := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ
  have htotal : T * radialMass n = 1 := by
    rw [← stdGaussian_direction_preimage MeasurableSet.univ, Set.preimage_univ, measure_univ]
  have hK : radialMass n = T⁻¹ := by
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact htotal)
  ext s hs
  rw [Measure.map_apply measurable_direction hs, stdGaussian_direction_preimage hs, hK,
    ArlibCommunity.Foundations.MarkovChainTheory.unifSphere, Measure.smul_apply, smul_eq_mul,
    ArlibCommunity.Foundations.MarkovChainTheory.sphereArea, mul_comm]

/-! ## The radius `u^{1/n}` -/

/-- **The radius law.** For `u` uniform on `[0, 1]`, `u^{1/n}` lies in `A ∩ (0, 1)` with
probability `n ∫_{A ∩ (0,1)} r^{n−1} dr`. -/
theorem unitLaw_root_preimage {n : Nat} (hn : 0 < n) {A : Set Real} (hA : MeasurableSet A) :
    volume.restrict (Icc (0 : Real) 1) {u | u ^ ((n : Real)⁻¹) ∈ A} =
      n * Measure.volumeIoiPow (n - 1) {r | (r : Real) < 1 ∧ (r : Real) ∈ A} := by
  have hn0 : n ≠ 0 := hn.ne'
  set s : Set Real := Ioo 0 1 ∩ A with hs_def
  have hs : MeasurableSet s := measurableSet_Ioo.inter hA
  -- the right side as an integral over `s`
  have hB : MeasurableSet {r : Ioi (0 : Real) | (r : Real) < 1 ∧ (r : Real) ∈ A} :=
    (measurableSet_lt measurable_subtype_coe measurable_const).inter
      (measurable_subtype_coe hA)
  have himage : Subtype.val '' {r : Ioi (0 : Real) | (r : Real) < 1 ∧ (r : Real) ∈ A} = s := by
    ext x
    simp only [mem_image, mem_ofPred_eq, Subtype.exists, mem_Ioi, exists_and_right,
      exists_eq_right, hs_def, mem_inter_iff, mem_Ioo]
    tauto
  rw [Measure.volumeIoiPow, withDensity_apply _ hB,
    setLIntegral_subtype measurableSet_Ioi _ (fun x : Real => ENNReal.ofReal (x ^ (n - 1))),
    himage, ← lintegral_const_mul _ (by fun_prop)]
  -- change variables `u = r^n`
  have hderiv : ∀ x ∈ s, HasDerivWithinAt (fun x : Real => x ^ n) ((n : Real) * x ^ (n - 1)) s x :=
    fun x _ => (hasDerivAt_pow n x).hasDerivWithinAt
  have hmono : MonotoneOn (fun x : Real => x ^ n) s := fun x hx y _ hxy =>
    pow_le_pow_left₀ hx.1.1.le hxy n
  have hcov := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hderiv hmono (fun _ => 1)
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter] at hcov
  have hint : ∫⁻ x in s, (n : ℝ≥0∞) * ENNReal.ofReal (x ^ (n - 1)) =
      ∫⁻ x in s, ENNReal.ofReal ((n : Real) * x ^ (n - 1)) := by
    refine setLIntegral_congr_fun hs fun x hx => ?_
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  rw [hint, ← hcov]
  -- the image of `s` under `r ↦ r^n`
  have himg : (fun x : Real => x ^ n) '' s = {u | u ^ ((n : Real)⁻¹) ∈ A} ∩ Ioo 0 1 := by
    ext u
    simp only [mem_image, hs_def, mem_inter_iff, mem_Ioo, mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨⟨hx0, hx1⟩, hxA⟩, rfl⟩
      refine ⟨by rwa [Real.pow_rpow_inv_natCast hx0.le hn0], pow_pos hx0 n,
        pow_lt_one₀ hx0.le hx1 hn0⟩
    · rintro ⟨hA', hu0, hu1⟩
      refine ⟨u ^ ((n : Real)⁻¹), ⟨⟨Real.rpow_pos_of_pos hu0 _, ?_⟩, hA'⟩,
        Real.rpow_inv_natCast_pow hu0.le hn0⟩
      exact Real.rpow_lt_one hu0.le hu1 (by positivity)
  rw [himg]
  have hpre : MeasurableSet {u : Real | u ^ ((n : Real)⁻¹) ∈ A} :=
    (measurable_id.pow_const _) hA
  rw [Measure.restrict_apply hpre]
  rw [one_mul]
  exact measure_congr (Filter.EventuallyEqSet.inter (ae_eq_refl _) (Ioo_ae_eq_Icc (μ := (volume : Measure Real)) (a := (0 : Real)) (b := 1)).symm)

variable {n : Nat} [NeZero n]

omit [NeZero n] in
theorem measurable_ballStartMap :
    Measurable (fun ω : EuclideanSpace Real (Fin n) × Real =>
      (ω.2 ^ ((n : Real)⁻¹) / ‖ω.1‖) • ω.1) := by
  fun_prop

/-- The ball-start map `(g, u) ↦ (u^{1/n} / ‖g‖) · g`. -/
noncomputable def ballStartMap (n : ℕ) (ω : EuclideanSpace Real (Fin n) × Real) :
    EuclideanSpace Real (Fin n) :=
  (ω.2 ^ ((n : Real)⁻¹) / ‖ω.1‖) • ω.1

/-- **A uniform point of the unit ball from a Gaussian vector and a uniform number.** If `g`
is a standard Gaussian vector and `u` an independent uniform number in `[0, 1]`, then
`(u^{1/n} / ‖g‖) · g` is uniform on the unit ball. -/
theorem ballStartMap_law :
    ((stdGaussian (EuclideanSpace Real (Fin n))).prod (volume.restrict (Icc (0 : Real) 1))).map
        (ballStartMap n) =
      ArlibCommunity.Foundations.Convex.uniformOn volume
        (ball (0 : EuclideanSpace Real (Fin n)) 1) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hF : ballStartMap n = fun ω => (ω.2 ^ ((n : Real)⁻¹) / ‖ω.1‖) • ω.1 := rfl
  -- along a direction `θ`: the probability that the start point lands in `S`
  let R : (S : Set (EuclideanSpace Real (Fin n))) → sphere (0 : EuclideanSpace Real (Fin n)) 1 →
      ℝ≥0∞ := fun S θ => volume.restrict (Icc (0 : Real) 1) {u | u ^ ((n : Real)⁻¹) • (θ : EuclideanSpace Real (Fin n)) ∈ S}
  ext S hS
  have hRset : MeasurableSet {p : sphere (0 : EuclideanSpace Real (Fin n)) 1 × Real |
      p.2 ^ ((n : Real)⁻¹) • (p.1 : EuclideanSpace Real (Fin n)) ∈ S} :=
    hS.preimage (by fun_prop)
  have hRm : Measurable (R S) := measurable_measure_prodMk_left hRset
  -- the Gaussian side: average over directions
  have hae : ∀ᵐ g ∂stdGaussian (EuclideanSpace Real (Fin n)), g ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, ofPred_eq_eq_singleton]
    rw [stdGaussian_apply n (measurableSet_singleton 0)]
    exact setLIntegral_measure_zero _ _ (measure_singleton 0)
  have hLHS : ((stdGaussian (EuclideanSpace Real (Fin n))).prod
      (volume.restrict (Icc (0 : Real) 1))).map (ballStartMap n) S = ∫⁻ θ, R S θ ∂ArlibCommunity.Foundations.MarkovChainTheory.unifSphere n := by
    rw [hF, Measure.map_apply measurable_ballStartMap hS,
      Measure.prod_apply (measurable_ballStartMap hS),
      ← stdGaussian_map_direction,
      lintegral_map hRm measurable_direction]
    refine lintegral_congr_ae (hae.mono fun g hg => ?_)
    change (volume.restrict (Icc (0 : Real) 1)) _ = (volume.restrict (Icc (0 : Real) 1)) _
    congr 1
    ext u
    simp [direction, directionVal, hg, div_eq_mul_inv,
      mul_smul]
  -- the radius law along each direction
  let B : Set (sphere (0 : EuclideanSpace Real (Fin n)) 1 × Ioi (0 : Real)) :=
    {p | (p.2 : Real) < 1 ∧ (p.2 : Real) • (p.1 : EuclideanSpace Real (Fin n)) ∈ S}
  have hB : MeasurableSet B :=
    (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) measurable_const).inter
      (hS.preimage (by fun_prop))
  have hR : ∀ θ, R S θ = n * Measure.volumeIoiPow (n - 1) (Prod.mk θ ⁻¹' B) := fun θ =>
    unitLaw_root_preimage hn (A := {r | r • (θ : EuclideanSpace Real (Fin n)) ∈ S})
      (hS.preimage (by fun_prop))
  -- polar coordinates
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd
    (volume : Measure (EuclideanSpace Real (Fin n)))
  rw [finrank_euclideanSpace_fin] at hmp
  have h0 : MeasurableSet ({0}ᶜ : Set (EuclideanSpace Real (Fin n))) :=
    (measurableSet_singleton 0).compl
  have himage : Subtype.val '' (homeomorphUnitSphereProd (EuclideanSpace Real (Fin n)) ⁻¹' B) =
      (S ∩ ball 0 1) \ {0} := by
    ext y
    simp only [mem_image, mem_preimage, Subtype.exists, mem_compl_iff, mem_singleton_iff,
      exists_and_right, exists_eq_right, B, mem_ofPred_eq, mem_sdiff, mem_inter_iff, mem_ball,
      dist_zero_right]
    constructor
    · rintro ⟨hy, hlt, hmem⟩
      simp only [homeomorphUnitSphereProd_apply_snd_coe,
        homeomorphUnitSphereProd_apply_fst_coe] at hlt hmem
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul] at hmem
      exact ⟨⟨hmem, hlt⟩, hy⟩
    · rintro ⟨⟨hmem, hlt⟩, hy⟩
      refine ⟨hy, ?_, ?_⟩
      · simpa using hlt
      · simp only [homeomorphUnitSphereProd_apply_snd_coe,
          homeomorphUnitSphereProd_apply_fst_coe]
        rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]
  have hprod : ((volume : Measure (EuclideanSpace Real (Fin n))).toSphere.prod
      (Measure.volumeIoiPow (n - 1))) B = volume (S ∩ ball 0 1) := by
    rw [← hmp.measure_preimage hB.nullMeasurableSet, comap_subtype_coe_apply h0, himage,
      measure_sdiff_null (measure_singleton 0)]
  -- assemble
  have hT : (volume : Measure (EuclideanSpace Real (Fin n))).toSphere univ =
      n * volume (ball (0 : EuclideanSpace Real (Fin n)) 1) := by
    rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]
  have hball0 : volume (ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ 0 :=
    (measure_ball_pos volume _ one_pos).ne'
  have hballtop : volume (ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hLHS, ArlibCommunity.Foundations.MarkovChainTheory.unifSphere, lintegral_smul_measure]
  simp_rw [hR]
  rw [lintegral_const_mul _ (measurable_measure_prodMk_left hB), ← Measure.prod_apply hB, hprod,
    ArlibCommunity.Foundations.MarkovChainTheory.sphereArea, hT,
    ArlibCommunity.Foundations.Convex.uniformOn_def, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hS, ENNReal.mul_inv (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))]
  rw [smul_eq_mul, mul_assoc, mul_left_comm _ (n : ℝ≥0∞), ← mul_assoc ((n : ℝ≥0∞)⁻¹),
    ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n), one_mul]

end ttc.ChargedCV18.GaussianSampling
