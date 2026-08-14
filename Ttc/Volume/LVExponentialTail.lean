/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.MomentRadiusTruncation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The exponential tail calculation in LV07 Lemma 5.7

This file isolates the final calculation after the KLS exponential-extremizer reduction.
The source evaluates the exponential quotient explicitly.  An equivalent shorter argument
translates the left-tail interval by `t`: the translated interval lies in the full support,
while `exp (gamma*x)` is multiplied by `exp (gamma*t)`.
-/

namespace Ttc.CVAdaptive

open MeasureTheory Set

/-- Translating an interval of an exponential weight by `d` multiplies its mass by
`exp (gamma*d)`. -/
theorem expWeight_interval_shift (gamma a b d : Real) :
    Real.exp (gamma * d) * (∫ x in a..b, Real.exp (gamma * x)) =
      ∫ x in (a + d)..(b + d), Real.exp (gamma * x) := by
  rw [← intervalIntegral.integral_comp_add_right
    (f := fun x : Real ↦ Real.exp (gamma * x)) d]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp
  rw [← Real.exp_add]
  congr 1
  ring

/-- The final one-sided exponential calculation needed in LV07 Lemma 5.7.

Here `a <= -t` says the left tail is nonempty, `0 <= b` makes its translate by `t` a
subinterval of the support, and `1 - 1/t <= gamma` is exactly the rate estimate obtained from
the endpoint/moment calculation in the paper. -/
theorem exponential_leftTail_mul_exp_le (gamma a b t : Real)
    (ht : 0 < t) (ha : a <= -t) (hb : 0 <= b) (hgamma : 1 - 1 / t <= gamma) :
    Real.exp (t - 1) * (∫ x in a..(-t), Real.exp (gamma * x)) <=
      ∫ x in a..b, Real.exp (gamma * x) := by
  have hrate : t - 1 <= gamma * t := by
    have := mul_le_mul_of_nonneg_right hgamma ht.le
    calc
      t - 1 = (1 - 1 / t) * t := by field_simp [ht.ne']
      _ <= gamma * t := this
  have hexp : Real.exp (t - 1) <= Real.exp (gamma * t) := Real.exp_le_exp.mpr hrate
  have htail0 : 0 <= ∫ x in a..(-t), Real.exp (gamma * x) :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ ↦ (Real.exp_pos _).le
  calc
    Real.exp (t - 1) * (∫ x in a..(-t), Real.exp (gamma * x)) <=
        Real.exp (gamma * t) * (∫ x in a..(-t), Real.exp (gamma * x)) :=
      mul_le_mul_of_nonneg_right hexp htail0
    _ = ∫ x in (a + t)..0, Real.exp (gamma * x) := by
      simpa using expWeight_interval_shift gamma a (-t) t
    _ <= ∫ x in a..b, Real.exp (gamma * x) := by
      have hat : a <= a + t := by linarith
      have hat0 : a + t <= 0 := by linarith
      exact intervalIntegral.integral_mono_interval hat hat0 hb
        (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos (gamma * x)).le)
        (Continuous.intervalIntegrable (by fun_prop) a b)

/-- The paper's endpoint estimate `gamma >= (a+1)/a` implies the rate condition used by
`exponential_leftTail_mul_exp_le` whenever the tail endpoint satisfies `a <= -t`. -/
theorem exponential_rate_of_endpoint {gamma a t : Real} (ht : 0 < t) (ha : a <= -t)
    (hgamma : (a + 1) / a <= gamma) : 1 - 1 / t <= gamma := by
  have ha0 : a < 0 := lt_of_le_of_lt ha (neg_lt_zero.mpr ht)
  have hbase : 1 - 1 / t <= (a + 1) / a := by
    have hinv : 1 / (-t) <= 1 / a :=
      one_div_le_one_div_of_neg_of_le (neg_lt_zero.mpr ht) ha
    have haid : (a + 1) / a = 1 + 1 / a := by
      rw [div_eq_mul_inv, add_mul, mul_inv_cancel₀ ha0.ne, one_mul]
      rw [one_div]
    rw [haid]
    simpa only [one_div, inv_neg, sub_eq_add_neg, add_comm] using add_le_add_left hinv 1
  exact hbase.trans hgamma

/-- Final LV exponential-tail bound in cross-multiplied form, after the endpoint estimate. -/
theorem exponential_leftTail_lv (gamma a b t : Real)
    (ht : 0 < t) (ha : a <= -t) (hb : 0 <= b)
    (hgamma : (a + 1) / a <= gamma) :
    Real.exp (t - 1) * (∫ x in a..(-t), Real.exp (gamma * x)) <=
      ∫ x in a..b, Real.exp (gamma * x) :=
  exponential_leftTail_mul_exp_le gamma a b t ht ha hb
    (exponential_rate_of_endpoint ht ha hgamma)

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.expWeight_interval_shift
#print axioms Ttc.CVAdaptive.exponential_leftTail_mul_exp_le
#print axioms Ttc.CVAdaptive.exponential_leftTail_lv
