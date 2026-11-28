/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.PlanarBox
import Arlib.Approximation.MulError
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! The area estimate from independent points of the enclosing square. -/

set_option autoImplicit false

noncomputable section

namespace ttc.Planar

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

/-- Area of the sampling square and the number of points in the estimate. -/
def boxArea (P : PolytopeData 2) : ℝ := 4 * radius P ^ 2

def trialCount (B eps delta : ℝ) : ℕ := ⌈3 * B * Real.log (2 / delta) / eps ^ 2⌉₊

theorem boxArea_pos (P : PolytopeData 2) : 0 < boxArea P := by
  unfold boxArea
  have := radius_one_le P
  positivity

theorem area_le_boxArea (P : PolytopeData 2) :
    volume P.cv18Body ≤ ENNReal.ofReal (boxArea P) := by
  rw [boxArea, ← volume_square ((by norm_num : (0 : ℝ) ≤ 1).trans (radius_one_le P))]
  exact measure_mono (cv18Body_subset_square P)

theorem one_le_area (P : PolytopeData 2) : 1 ≤ (volume P.cv18Body).toReal := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (area_le_boxArea P)
  simpa using ENNReal.toReal_mono hfin (one_le_volume_cv18Body P)

/-- Fraction of the sampling square occupied by the body. -/
def hitProbability (P : PolytopeData 2) : I :=
  ⟨(volume P.cv18Body).toReal / boxArea P, div_nonneg ENNReal.toReal_nonneg (boxArea_pos P).le,
    (div_le_one (boxArea_pos P)).2 (by
      simpa [ENNReal.toReal_ofReal (boxArea_pos P).le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (area_le_boxArea P))⟩

/-- The outcome of checking whether the point lies in the normalized body. -/
def hit (P : PolytopeData 2) (uv : ℝ × ℝ) : Bool := by
  classical
  exact decide (pointFromUnits (radius P) uv ∈ P.cv18Body)

theorem measurable_hit (P : PolytopeData 2) : Measurable (hit P) := by
  classical
  apply measurable_to_countable'
  intro b
  have htrue : hit P ⁻¹' {true} = pointFromUnits (radius P) ⁻¹' P.cv18Body := by
    ext uv; simp [hit]
  have h := measurable_pointFromUnits (radius P) P.cv18Body_measurable
  cases b
  · rw [show ({false} : Set Bool) = {true}ᶜ by ext v; cases v <;> simp, preimage_compl, htrue]
    exact h.compl
  · rw [htrue]
    exact h

/-- One draw from the square and one membership test give a Bernoulli flag. -/
theorem map_hit (P : PolytopeData 2) :
    ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))).map (hit P) =
      bernoulliMeasure true false (hitProbability P) := by
  classical
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  have : IsProbabilityMeasure ((μ.prod μ).map (hit P)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_hit P).aemeasurable).2 inferInstance
  change (μ.prod μ).map (hit P) = _
  have ht : ((μ.prod μ).map (hit P)) {true} = ENNReal.ofReal (hitProbability P : ℝ) := by
    rw [Measure.map_apply (measurable_hit P) (measurableSet_singleton _),
      show hit P ⁻¹' {true} = pointFromUnits (radius P) ⁻¹' P.cv18Body by ext uv; simp [hit],
      ← Measure.map_apply (measurable_pointFromUnits (radius P)) P.cv18Body_measurable]
    have hR : 0 < radius P := zero_lt_one.trans_le (radius_one_le P)
    change ((μ.prod μ).map (pointFromUnits (radius P))) P.cv18Body = _
    rw [show (μ.prod μ).map (pointFromUnits (radius P)) = _ from pointFromUnits_map hR,
      Measure.smul_apply, Measure.restrict_apply P.cv18Body_measurable,
      inter_eq_left.mpr (cv18Body_subset_square P)]
    have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (area_le_boxArea P)
    change (ENNReal.ofReal (boxArea P))⁻¹ * volume P.cv18Body =
      ENNReal.ofReal ((volume P.cv18Body).toReal / boxArea P)
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr (boxArea_pos P).le),
      ENNReal.ofReal_toReal hfin, ENNReal.ofReal_inv_of_pos (boxArea_pos P)]
  have hb : (bernoulliMeasure true false (hitProbability P)) {true} =
      ENNReal.ofReal (hitProbability P : ℝ) := by
    rw [bernoulliMeasure_apply _ (measurableSet_singleton true)]
    simp only [mem_singleton_iff, Bool.false_eq_true, ite_false, ite_true, ENNReal.ofReal,
      Real.toNNReal_of_nonneg (hitProbability P).2.1]
    rfl
  refine Measure.ext_iff_singleton.mpr fun b => ?_
  cases b
  · rw [show ({false} : Set Bool) = {true}ᶜ by ext v; cases v <;> simp,
      prob_compl_eq_one_sub (measurableSet_singleton true),
      prob_compl_eq_one_sub (measurableSet_singleton true), ht, hb]
  · rw [ht, hb]

/-- The estimate from the flags, with total square area `B`. -/
def estimateFromHits (B : ℝ) {N : ℕ} (v : Fin N → Bool) : ℝ :=
  B * ((hits v : ℝ) / N)

def areaLaw (P : PolytopeData 2) (eps delta : ℝ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin (trialCount (boxArea P) eps delta) =>
    bernoulliMeasure true false (hitProbability P))).map (estimateFromHits (boxArea P))

instance (P : PolytopeData 2) (eps delta : ℝ) : IsProbabilityMeasure (areaLaw P eps delta) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2 inferInstance

/-- With this many points, the estimated area of the normalized body has
relative error at most `eps` except with probability at most `delta`. -/
theorem areaLaw_accuracy (P : PolytopeData 2) {eps delta : ℝ} (he : 0 < eps) (he1 : eps ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) :
    (areaLaw P eps delta).real (Arlib.relErr eps (volume P.cv18Body).toReal) ≥ 1 - delta := by
  let B := boxArea P
  let N := trialCount B eps delta
  let A := (volume P.cv18Body).toReal
  let q := hitProbability P
  have hB : 0 < B := boxArea_pos P
  have hA : 1 ≤ A := one_le_area P
  have hq : (q : ℝ) = A / B := rfl
  have hl : 0 < Real.log (2 / delta) :=
    Real.log_pos ((lt_div_iff₀ hd).2 (by linarith))
  have hceil : 3 * B * Real.log (2 / delta) / eps ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hpos : 0 < (N : ℝ) := (by positivity : 0 < 3 * B * Real.log (2 / delta) / eps ^ 2).trans_le hceil
  have hmean : Real.log (2 / delta) ≤ eps ^ 2 * ((N : ℝ) * q) / 3 := by
    have h₁ := (div_le_iff₀ (sq_pos_of_pos he)).mp hceil
    have h₂ : 3 * (B * Real.log (2 / delta)) ≤ (N : ℝ) * eps ^ 2 * A := calc
      3 * (B * Real.log (2 / delta)) ≤ (N : ℝ) * eps ^ 2 := by linarith
      _ ≤ (N : ℝ) * eps ^ 2 * A := le_mul_of_one_le_right (by positivity) hA
    rw [hq, le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    simp only [← mul_div_assoc]
    apply (le_div_iff₀ hB).2
    convert h₂ using 1 <;> ring
  have htail : 2 * Real.exp (-(eps ^ 2 * ((N : ℝ) * q)) / 3) ≤ delta := calc
    _ ≤ 2 * Real.exp (-Real.log (2 / delta)) := by
      gcongr
      linarith
    _ = delta := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
  let S := Arlib.relErr eps A
  have hS : MeasurableSet S := measurableSet_Icc
  have hv (v : Fin N → Bool) :
      estimateFromHits B v ∈ S ↔ |(hits v : ℝ) - (N : ℝ) * q| ≤ eps * ((N : ℝ) * q) := by
    have hfactor : 0 < B / (N : ℝ) := div_pos hB hpos
    have hleft : estimateFromHits B v - A =
        (B / (N : ℝ)) * ((hits v : ℝ) - (N : ℝ) * q) := by
      rw [estimateFromHits, hq]
      field_simp
    have hright : eps * A = (B / (N : ℝ)) * (eps * ((N : ℝ) * q)) := by
      rw [hq]
      field_simp
    change estimateFromHits B v ∈ Arlib.relErr eps A ↔ _
    rw [Arlib.Approximation.mem_relErr_iff_abs, hleft, hright, abs_mul, abs_of_pos hfactor, mul_le_mul_iff_of_pos_left hfactor]
  have hbad : (estimateFromHits B : (Fin N → Bool) → ℝ) ⁻¹' Sᶜ =
      {v | eps * ((N : ℝ) * q) < |(hits v : ℝ) - (N : ℝ) * q|} := by
    ext v
    simp [hv v, not_le]
  have hc : (areaLaw P eps delta).real Sᶜ ≤ delta := by
    rw [areaLaw, measureReal_def,
      Measure.map_apply (measurable_of_countable _) hS.compl, hbad]
    exact (hits_chernoff N q he he1).trans htail
  rw [measureReal_compl hS, probReal_univ] at hc
  change 1 - delta ≤ (areaLaw P eps delta).real S
  linarith

end ttc.Planar
