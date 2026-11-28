/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.CV18NormalizedPolytope
import ttc.Analysis.PlanarConcentration
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Geometry and relative-error analysis of direct sampling for a planar component. -/

set_option autoImplicit false

noncomputable section

namespace ttc.Planar

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal unitInterval

abbrev Point := EuclideanSpace ℝ (Fin 2)

def pairEquiv : (ℝ × ℝ) ≃ᵐ Point :=
  (MeasurableEquiv.piFinTwo (fun _ => ℝ)).symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

theorem pairEquiv_preserves : MeasurePreserving pairEquiv :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp
    (volume_preserving_piFinTwo (fun _ => ℝ)).symm

/-- The axis-aligned square with half-side `R`. -/
def square (R : ℝ) : Set Point := {x | ∀ i, x i ∈ Icc (-R) R}

theorem measurableSet_square (R : ℝ) : MeasurableSet (square R) := by
  rw [show square R = ⋂ i : Fin 2, (fun x : Point => x i) ⁻¹' Icc (-R) R by
    ext x; simp [square]]
  exact MeasurableSet.iInter fun i => (by fun_prop : Measurable fun x : Point => x i) measurableSet_Icc

theorem pairEquiv_preimage_square (R : ℝ) :
    pairEquiv ⁻¹' square R = Icc (-R) R ×ˢ Icc (-R) R := by
  ext ⟨x, y⟩
  simp only [mem_preimage, square, mem_ofPred_eq, mem_prod, Fin.forall_fin_two]
  rfl

theorem volume_square {R : ℝ} (hR : 0 ≤ R) : volume (square R) = ENNReal.ofReal (4 * R ^ 2) := by
  rw [← pairEquiv_preserves.measure_preimage (measurableSet_square R).nullMeasurableSet,
    pairEquiv_preimage_square, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith : 0 ≤ R - -R)]
  congr 1
  ring

/-- The enclosing square uses a certified bound on the normalized radius. -/
def radius (P : PolytopeData 2) : ℝ := max 1 (P.BoundingRadius / P.inradius)

theorem radius_one_le (P : PolytopeData 2) : 1 ≤ radius P := le_max_left _ _

theorem cv18Body_subset_square (P : PolytopeData 2) : P.cv18Body ⊆ square (radius P) := by
  intro x hx i
  have h := P.cv18Body_subset_boundingBall hx
  rw [mem_closedBall, dist_zero_right] at h
  change -radius P ≤ x i ∧ x i ≤ radius P
  rw [← abs_le]
  exact ((PiLp.norm_apply_le x i).trans h).trans (le_max_right _ _)

theorem halfSquare_subset_unitBall : square (1 / 2) ⊆ closedBall (0 : Point) 1 := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  have hi (i : Fin 2) : |x i| ≤ 1 / 2 := abs_le.mpr (hx i)
  have hs (i : Fin 2) : x i ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg (x i)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 (hi i)
  have h := EuclideanSpace.real_norm_sq_eq x
  rw [Fin.sum_univ_two] at h
  nlinarith [hs 0, hs 1, norm_nonneg x]

theorem one_le_volume_cv18Body (P : PolytopeData 2) : 1 ≤ volume P.cv18Body := by
  have hm := measure_mono (μ := (volume : Measure Point))
    (halfSquare_subset_unitBall.trans P.closedUnitBall_subset_cv18Body)
  rwa [volume_square (by norm_num : (0 : ℝ) ≤ 1 / 2), show 4 * (1 / 2 : ℝ) ^ 2 = 1 by norm_num,
    ENNReal.ofReal_one] at hm

/-- Scalar affine transport from the unit interval to a scaled side. -/
def coordinate (R u : ℝ) : ℝ := 2 * R * u - R

theorem map_uniform_coordinate {R : ℝ} (hR : 0 < R) :
    (volume.restrict (Icc (0 : ℝ) 1)).map (coordinate R) =
      ENNReal.ofReal ((2 * R)⁻¹) • (volume.restrict (Icc (-R) R)) := by
  have hf : Measurable (coordinate R) := by unfold coordinate; fun_prop
  ext s hs
  rw [Measure.map_apply hf hs, Measure.restrict_apply (hf hs), Measure.smul_apply,
    Measure.restrict_apply hs]
  have hI : coordinate R ⁻¹' Icc (-R) R = Icc 0 1 := by
    ext v
    simp only [mem_preimage, mem_Icc, coordinate]
    constructor <;> intro h <;> constructor
    · exact nonneg_of_mul_nonneg_right (by linarith [h.1]) (by positivity : 0 < 2 * R)
    · have hb : 0 ≤ 2 * R * (1 - v) := by linarith [h.2]
      have := nonneg_of_mul_nonneg_right hb (by positivity : 0 < 2 * R)
      linarith
    · linarith [mul_nonneg (by positivity : 0 ≤ 2 * R) h.1]
    · linarith [mul_nonneg (by positivity : 0 ≤ 2 * R) (sub_nonneg.mpr h.2)]
  rw [← hI, ← preimage_inter]
  change volume ((fun v : ℝ => 2 * R * v) ⁻¹'
    ((fun x : ℝ => x + -R) ⁻¹' (s ∩ Icc (-R) R))) = _
  rw [Real.volume_preimage_mul_left (by positivity : (2 * R : ℝ) ≠ 0),
    abs_of_pos (by positivity), measure_preimage_add_right]
  rfl

/-- A pair of uniform numbers becomes a point of the scaled square. -/
def pointFromUnits (R : ℝ) (uv : ℝ × ℝ) : Point :=
  pairEquiv (coordinate R uv.1, coordinate R uv.2)

theorem measurable_pointFromUnits (R : ℝ) : Measurable (pointFromUnits R) :=
  pairEquiv.measurable.comp (by unfold coordinate; fun_prop)

/-- The generated point has the normalized Lebesgue law on the square. -/
theorem pointFromUnits_map {R : ℝ} (hR : 0 < R) :
    ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))).map
      (pointFromUnits R) =
    (ENNReal.ofReal (4 * R ^ 2))⁻¹ • volume.restrict (square R) := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have hf : Measurable (coordinate R) := by unfold coordinate; fun_prop
  change ((μ.prod μ).map (pairEquiv ∘ Prod.map (coordinate R) (coordinate R))) = _
  rw [← Measure.map_map pairEquiv.measurable (hf.prodMap hf), ← Measure.map_prod_map μ μ hf hf]
  dsimp only [μ]
  rw [map_uniform_coordinate hR, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, ← ENNReal.ofReal_mul (by positivity), Measure.prod_restrict,
    ← Measure.volume_eq_prod, Measure.map_smul _ pairEquiv.measurable.aemeasurable]
  have hmap : ((volume : Measure (ℝ × ℝ)).restrict (Icc (-R) R ×ˢ Icc (-R) R)).map pairEquiv
      = volume.restrict (square R) := by
    ext s hs
    rw [Measure.map_apply pairEquiv.measurable hs, Measure.restrict_apply (pairEquiv.measurable hs),
      Measure.restrict_apply hs, ← pairEquiv_preimage_square, ← preimage_inter,
      pairEquiv_preserves.measure_preimage (hs.inter (measurableSet_square R)).nullMeasurableSet]
  rw [hmap]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 4 * R ^ 2)]
  congr 1
  field_simp <;> norm_num

end ttc.Planar
