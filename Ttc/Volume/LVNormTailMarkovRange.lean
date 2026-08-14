/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.MomentRadiusTruncation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The elementary range of the Lovasz--Vempala norm tail

The proof of Lovasz--Vempala (2007), Lemma 5.7 splits at `t = 3`.  On `1 < t <= 3`
the claimed exponential estimate is just Markov's inequality applied to `||X||^2`.
This file records that part in arbitrary dimension and for an arbitrary probability measure.

The `t > 3` part of LV Lemma 5.7 uses a one-dimensional exponential-extremizer variant of
Kannan--Lovasz--Simonovits Lemma 2.6.  That extremizer theorem is not currently available in
the repository; the general localization stack returns an arbitrary log-concave profile and
therefore cannot replace it in this argument.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]

/-- Markov's inequality in exactly the scaled second-moment form used in the first part of
LV07 Lemma 5.7. -/
theorem norm_tail_measureReal_le_inv_sq (mu : Measure E) [IsProbabilityMeasure mu]
    {R t : Real} (hR : 0 < R) (ht : 0 < t)
    (hint : Integrable (fun x : E => ‖x‖ ^ 2) mu)
    (hmoment : (∫ x, ‖x‖ ^ 2 ∂mu) <= R ^ 2) :
    mu.real {x | t * R < ‖x‖} <= 1 / t ^ 2 := by
  have htr : 0 < t * R := mul_pos ht hR
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := mu) (f := fun x : E => ‖x‖ ^ 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖x‖) hint ((t * R) ^ 2)
  have hsub : {x : E | t * R < ‖x‖} ⊆ {x | (t * R) ^ 2 <= ‖x‖ ^ 2} := by
    intro x hx
    exact le_of_lt ((sq_lt_sq₀ htr.le (norm_nonneg x)).2 hx)
  have hmono : mu.real {x : E | t * R < ‖x‖} <=
      mu.real {x | (t * R) ^ 2 <= ‖x‖ ^ 2} := measureReal_mono hsub
  have hmul : (t * R) ^ 2 * mu.real {x : E | t * R < ‖x‖} <= R ^ 2 :=
    calc
      (t * R) ^ 2 * mu.real {x : E | t * R < ‖x‖}
          <= (t * R) ^ 2 * mu.real {x | (t * R) ^ 2 <= ‖x‖ ^ 2} :=
            mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
      _ <= ∫ x, ‖x‖ ^ 2 ∂mu := hmarkov
      _ <= R ^ 2 := hmoment
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  apply (le_div_iff₀ ht2).2
  calc
    mu.real {x : E | t * R < ‖x‖} * t ^ 2
        = ((t * R) ^ 2 * mu.real {x : E | t * R < ‖x‖}) / R ^ 2 := by
          field_simp [hR.ne']
    _ <= R ^ 2 / R ^ 2 := div_le_div_of_nonneg_right hmul hR2.le
    _ = 1 := div_self hR2.ne'

/-- The elementary `1 < t <= 3` branch of LV07 Lemma 5.7.  Log-concavity is not needed in
this range. -/
theorem norm_tail_measureReal_le_exp_of_le_three (mu : Measure E) [IsProbabilityMeasure mu]
    {R t : Real} (hR : 0 < R) (ht1 : 1 < t) (ht3 : t <= 3)
    (hint : Integrable (fun x : E => ‖x‖ ^ 2) mu)
    (hmoment : (∫ x, ‖x‖ ^ 2 ∂mu) <= R ^ 2) :
    mu.real {x | t * R < ‖x‖} <= Real.exp (1 - t) := by
  refine (norm_tail_measureReal_le_inv_sq mu hR (by linarith) hint hmoment).trans ?_
  rw [div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < t))]
  have hcalc : 1 <= t ^ 2 * Real.exp (1 - t) := by
    have hlog : Real.log (t ^ 2) = 2 * Real.log t := by
      rw [Real.log_pow]
      norm_num
    rw [← Real.exp_log (sq_pos_of_pos (by linarith : 0 < t)), hlog, ← Real.exp_add]
    rw [Real.one_le_exp_iff]
    have hlog3 : 1 < Real.log 3 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : Real) < 3)]
      exact Real.exp_one_lt_three
    let a : Real := (3 - t) / 2
    let b : Real := (t - 1) / 2
    have ha : 0 <= a := by dsimp [a]; linarith
    have hb : 0 <= b := by dsimp [b]; linarith
    have hab : a + b = 1 := by dsimp [a, b]; ring
    have hcomb : a * 1 + b * 3 = t := by dsimp [a, b]; ring
    have hconc := strictConcaveOn_log_Ioi.concaveOn.2
      (show (1 : Real) ∈ Set.Ioi 0 by norm_num)
      (show (3 : Real) ∈ Set.Ioi 0 by norm_num) ha hb hab
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hconc
    rw [hcomb] at hconc
    nlinarith [mul_le_mul_of_nonneg_left hlog3.le hb]
  nlinarith

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.norm_tail_measureReal_le_inv_sq
#print axioms Ttc.CVAdaptive.norm_tail_measureReal_le_exp_of_le_three
