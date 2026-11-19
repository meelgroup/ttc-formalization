import ttc.Analysis.HitAndRunStep
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # The start point is uniform on the unit ball

`ballStart` (`Model/Prelude.lean`) returns `(u^{1/n} / ‖g‖) · g` for a standard Gaussian
vector `g` and an independent uniform `u ∈ [0, 1]`. This file proves:

* its cost is exactly `4n + 3`;
* its law (`ballStartLaw`) is the uniform law on the unit ball.

The proof: the direction `g/‖g‖` is uniform on the sphere (`GaussianDirection`), the radius
`u^{1/n}` has density `n r^{n−1}` on `(0, 1)` (a change of variables `u = r^n`), and in polar
coordinates the uniform law on the ball is exactly the product of these two laws. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace ttc

namespace BallStart

/-! ## Value and cost -/

theorem ballStart_value {n : Nat} (g : EuclideanSpace Real (Fin n)) (u : Real) :
    WithLp.toLp 2 (ballStart n (WithLp.ofLp g) u).value =
      (u ^ ((n : Real)⁻¹) / ‖g‖) • g := by
  have hnorm : ‖g‖ = Real.sqrt (dotProduct (WithLp.ofLp g) (WithLp.ofLp g)) := by
    rw [EuclideanSpace.norm_eq]
    simp [dotProduct, sq]
  ext i
  simp [ballStart, Counted.forEach, Counted.mul, Counted.div, Counted.sqrt, Counted.root,
    Counted.dot_value, Counted.draw, hnorm]

theorem ballStart_cost {m : Nat} (g : Fin (m + 1) → Real) (u : Real) :
    (ballStart (m + 1) g u).cost = 4 * (m + 1) + 3 := by
  simp only [ballStart, Counted.bind_eq, Counted.andThen_cost, Counted.draw, Counted.dot_cost,
    Counted.sqrt, Counted.root, Counted.div, Counted.forEach, Counted.mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  ring

/-- **The start point costs exactly `4n + 3` operations** (`n ≥ 1`), including the `n + 1`
random numbers it reads. -/
theorem ballStartCost_eq {n : Nat} (hn : 0 < n) : ballStartCost n = 4 * n + 3 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  simp only [zero_add, ballStartCost, ballStart_cost, ciSup_const]

/-! ## The radius `u^{1/n}` -/

/-- **The radius law.** For `u` uniform on `[0, 1]`, `u^{1/n}` lies in `A ∩ (0, 1)` with
probability `n ∫_{A ∩ (0,1)} r^{n−1} dr`. -/
theorem unitLaw_root_preimage {n : Nat} (hn : 0 < n) {A : Set Real} (hA : MeasurableSet A) :
    HitAndRunLaw.unitLaw {u | u ^ ((n : Real)⁻¹) ∈ A} =
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
    simp only [mem_image, mem_setOf_eq, Subtype.exists, mem_Ioi, exists_and_right,
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
    simp only [mem_image, hs_def, mem_inter_iff, mem_Ioo, mem_setOf_eq]
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
  change volume.restrict (Icc (0 : Real) 1) _ = _
  rw [Measure.restrict_apply hpre]
  rw [one_mul]
  exact measure_congr (Filter.EventuallyEqSet.inter (ae_eq_refl _) (Ioo_ae_eq_Icc (μ := (volume : Measure Real)) (a := (0 : Real)) (b := 1)).symm)

/-! ## The law of the start point -/

variable {n : Nat} [NeZero n]

omit [NeZero n] in
theorem measurable_ballStartMap :
    Measurable (fun ω : EuclideanSpace Real (Fin n) × Real =>
      (ω.2 ^ ((n : Real)⁻¹) / ‖ω.1‖) • ω.1) := by
  fun_prop

/-- **The start point is uniform on the unit ball.** -/
theorem ballStartLaw_eq :
    ballStartLaw n =
      ArlibCommunity.Foundations.Convex.uniformOn volume
        (ball (0 : EuclideanSpace Real (Fin n)) 1) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hF : (fun ω : EuclideanSpace Real (Fin n) × Real =>
      WithLp.toLp 2 (ballStart n (WithLp.ofLp ω.1) ω.2).value) =
      fun ω => (ω.2 ^ ((n : Real)⁻¹) / ‖ω.1‖) • ω.1 :=
    funext fun ω => ballStart_value ω.1 ω.2
  -- along a direction `θ`: the probability that the start point lands in `S`
  let R : (S : Set (EuclideanSpace Real (Fin n))) → sphere (0 : EuclideanSpace Real (Fin n)) 1 →
      ℝ≥0∞ := fun S θ => HitAndRunLaw.unitLaw {u | u ^ ((n : Real)⁻¹) • (θ : EuclideanSpace Real (Fin n)) ∈ S}
  ext S hS
  have hRset : MeasurableSet {p : sphere (0 : EuclideanSpace Real (Fin n)) 1 × Real |
      p.2 ^ ((n : Real)⁻¹) • (p.1 : EuclideanSpace Real (Fin n)) ∈ S} :=
    hS.preimage (by fun_prop)
  have hRm : Measurable (R S) := measurable_measure_prodMk_left hRset
  -- the Gaussian side: average over directions
  have hae : ∀ᵐ g ∂stdGaussian (EuclideanSpace Real (Fin n)), g ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, ofPred_eq_eq_singleton]
    rw [GaussianDirection.stdGaussian_apply n (measurableSet_singleton 0)]
    exact setLIntegral_measure_zero _ _ (measure_singleton 0)
  have hLHS : ballStartLaw n S = ∫⁻ θ, R S θ ∂ArlibCommunity.Foundations.MarkovChainTheory.unifSphere n := by
    rw [ballStartLaw, hF, Measure.map_apply measurable_ballStartMap hS,
      Measure.prod_apply (measurable_ballStartMap hS),
      ← GaussianDirection.stdGaussian_map_direction,
      lintegral_map hRm GaussianDirection.measurable_direction]
    refine lintegral_congr_ae (hae.mono fun g hg => ?_)
    change HitAndRunLaw.unitLaw _ = HitAndRunLaw.unitLaw _
    congr 1
    ext u
    simp [GaussianDirection.direction, GaussianDirection.directionVal, hg, div_eq_mul_inv,
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
      exists_and_right, exists_eq_right, B, mem_setOf_eq, mem_diff, mem_inter_iff, mem_ball,
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

end BallStart

/-- The charge for one sampler attempt is at most its closed form. -/
theorem PolytopeData.samplingAttemptCost_le {n : Nat} (hn : 0 < n) (P : PolytopeData n)
    (b : Nat) (eta : Real) (steps : Nat) :
    P.samplingAttemptCost b eta steps ≤
      TTCRuntime.samplingAttemptOperations n P.presentation.facetCount steps := by
  have hstep := (P.hitAndRunPresentation b eta).hitAndRunStepCost_le hn
  rw [PolytopeData.samplingAttemptCost, HalfspacePresentation.memberCost_eq hn,
    BallStart.ballStartCost_eq hn, TTCRuntime.samplingAttemptOperations,
    TTCRuntime.ballStartOperations, TTCRuntime.hitAndRunStepOperations,
    TTCRuntime.rejectionTestOperations]
  have : steps * (P.hitAndRunPresentation b eta).hitAndRunStepCost ≤
      steps * (4 * n * P.presentation.facetCount + 4 * P.presentation.facetCount + 6 * n + 9) :=
    Nat.mul_le_mul_left _ hstep
  simp only [PolytopeData.scaledPresentation] at *
  omega

end ttc
