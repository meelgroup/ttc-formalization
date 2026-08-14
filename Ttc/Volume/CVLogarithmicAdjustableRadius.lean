/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVExplicitAdjustableRadius

/-!
# A logarithmic adjustable truncation radius

The elementary explicit selector `A / b + 3` is convenient, but its square is quadratic
in the number `A` of sampler calls.  The Gaussian relative-tail estimate actually permits
a logarithmic selector.  For `0 < b <= A` and positive dimension, set

`q² = 4 + 4 log (A / b) / n`.

Using `log q <= q² / 4` for `q >= 2` gives

`q * exp (-(q² - 1) / 2) <= exp (-log (A / b) / n)`.

After taking the `n`th power, the accumulated tail over `A` calls is at most `b`.
This is the radius dependence needed to retain the polylogarithmic overhead in the
Cousins--Vempala runtime, rather than merely proving an unspecified polynomial bound.
-/

namespace Ttc.CVAdaptive

open Arlib.GaussianCooling

variable {n : Nat}

/-- Adjustable radius whose square grows only as `log (A / b) / n`. -/
noncomputable def logarithmicAdaptiveRadiusQ (n : Nat) (A b : Real) : Real :=
  Real.sqrt (4 + 4 * Real.log (A / b) / (n : Real))

theorem logarithmicAdaptiveRadiusQ_sq (hn : 1 <= n) {A b : Real}
    (hb : 0 < b) (hbA : b <= A) :
    logarithmicAdaptiveRadiusQ n A b ^ 2 =
      4 + 4 * Real.log (A / b) / (n : Real) := by
  have hn0 : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hratio : 1 <= A / b := (le_div_iff₀ hb).2 (by simpa using hbA)
  have hlog : 0 <= Real.log (A / b) := Real.log_nonneg hratio
  unfold logarithmicAdaptiveRadiusQ
  exact Real.sq_sqrt (by positivity)

theorem two_le_logarithmicAdaptiveRadiusQ (hn : 1 <= n) {A b : Real}
    (hb : 0 < b) (hbA : b <= A) :
    2 <= logarithmicAdaptiveRadiusQ n A b := by
  have hn0 : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hratio : 1 <= A / b := (le_div_iff₀ hb).2 (by simpa using hbA)
  have hlog : 0 <= Real.log (A / b) := Real.log_nonneg hratio
  have hterm : 0 <= 4 * Real.log (A / b) / (n : Real) :=
    div_nonneg (mul_nonneg (by norm_num) hlog) hn0.le
  have hfour : (4 : Real) <= 4 + 4 * Real.log (A / b) / (n : Real) := by linarith
  have hsqrtFour : Real.sqrt 4 = (2 : Real) := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    norm_num
  rw [← hsqrtFour, logarithmicAdaptiveRadiusQ]
  exact Real.sqrt_le_sqrt hfour

private theorem gaussianRadiusBase_le_exp_log_div {n : Nat} (hn : 1 <= n)
    {A b q : Real}
    (hq2 : q ^ 2 = 4 + 4 * Real.log (A / b) / (n : Real)) (hq : 2 <= q) :
    q * Real.exp (-(q ^ 2 - 1) / 2) <=
      Real.exp (-Real.log (A / b) / (n : Real)) := by
  have hn0 : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hlogq0 := Real.log_le_sub_one_of_pos hq0
  have hquad : q - 1 <= q ^ 2 / 4 := by
    nlinarith [sq_nonneg (q - 2)]
  have hlogq : Real.log q <= q ^ 2 / 4 := hlogq0.trans hquad
  have hquarter : q ^ 2 / 4 = 1 + Real.log (A / b) / (n : Real) := by
    rw [hq2]
    ring
  have hexponent :
      Real.log q - (q ^ 2 - 1) / 2 <= -Real.log (A / b) / (n : Real) := by
    calc
      Real.log q - (q ^ 2 - 1) / 2
          <= q ^ 2 / 4 - (q ^ 2 - 1) / 2 := sub_le_sub_right hlogq _
      _ = 1 / 2 - q ^ 2 / 4 := by ring
      _ = -1 / 2 - Real.log (A / b) / (n : Real) := by rw [hquarter]; ring
      _ <= -Real.log (A / b) / (n : Real) := by
        rw [show -1 / 2 - Real.log (A / b) / (n : Real) =
          -Real.log (A / b) / (n : Real) - 1 / 2 by ring]
        exact sub_le_self _ (by norm_num)
  calc
    q * Real.exp (-(q ^ 2 - 1) / 2) =
        Real.exp (Real.log q - (q ^ 2 - 1) / 2) := by
          rw [show -(q ^ 2 - 1) / 2 = -((q ^ 2 - 1) / 2) by ring,
            Real.exp_neg, Real.exp_sub, Real.exp_log hq0]
          simp only [div_eq_mul_inv]
    _ <= Real.exp (-Real.log (A / b) / (n : Real)) :=
      Real.exp_le_exp.mpr hexponent

/-- The logarithmic selector spends total relative truncation error at most `b` over
`A` sampler calls. -/
theorem logarithmicAdaptiveRadiusQ_tailFits (hn : 1 <= n) {A b : Real}
    (hA : 0 < A) (hb : 0 < b) (hbA : b <= A) :
    AdjustableRadiusTailFits n A b (logarithmicAdaptiveRadiusQ n A b) := by
  let q := logarithmicAdaptiveRadiusQ n A b
  have hn0 : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hq2 : q ^ 2 = 4 + 4 * Real.log (A / b) / (n : Real) :=
    logarithmicAdaptiveRadiusQ_sq hn hb hbA
  have hq : 2 <= q := two_le_logarithmicAdaptiveRadiusQ hn hb hbA
  have hbase := gaussianRadiusBase_le_exp_log_div hn hq2 hq
  have hbase0 : 0 <= q * Real.exp (-(q ^ 2 - 1) / 2) := by positivity
  have hpow :
      (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n <=
        Real.exp (-Real.log (A / b) / (n : Real)) ^ n := by
    exact pow_le_pow_left₀ hbase0 hbase n
  have hexppow : Real.exp (-Real.log (A / b) / (n : Real)) ^ n = b / A := by
    rw [← Real.exp_nat_mul]
    have hnne : (n : Real) ≠ 0 := ne_of_gt hn0
    rw [show (n : Real) * (-Real.log (A / b) / (n : Real)) = -Real.log (A / b) by
      field_simp]
    rw [Real.exp_neg, Real.exp_log (div_pos hA hb)]
    field_simp
  constructor
  · linarith
  · calc
      A * (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n
          <= A * Real.exp (-Real.log (A / b) / (n : Real)) ^ n := by
            gcongr
      _ = A * (b / A) := by rw [hexppow]
      _ = b := by field_simp

/-- The squared conductance-radius factor is logarithmic in the number of calls.  The
constant `80` covers the sampler's minimum denominator factor `8`. -/
theorem max_eight_two_logarithmicAdaptiveRadiusQ_sq_le (hn : 1 <= n) {A b : Real}
    (hb : 0 < b) (hbA : b <= A) :
    max 8 (2 * logarithmicAdaptiveRadiusQ n A b) ^ 2 <=
      80 + 16 * Real.log (A / b) / (n : Real) := by
  let q := logarithmicAdaptiveRadiusQ n A b
  have hn0 : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hratio : 1 <= A / b := (le_div_iff₀ hb).2 (by simpa using hbA)
  have hlog : 0 <= Real.log (A / b) := Real.log_nonneg hratio
  have hq2 : q ^ 2 = 4 + 4 * Real.log (A / b) / (n : Real) :=
    logarithmicAdaptiveRadiusQ_sq hn hb hbA
  rw [max_def]
  split_ifs with h
  · have hterm : 0 <= 16 * Real.log (A / b) / (n : Real) :=
      div_nonneg (mul_nonneg (by norm_num) hlog) hn0.le
    change (2 * q) ^ 2 <= 80 + 16 * Real.log (A / b) / (n : Real)
    rw [mul_pow, hq2]
    calc
      2 ^ 2 * (4 + 4 * Real.log (A / b) / (n : Real)) =
          16 + 16 * Real.log (A / b) / (n : Real) := by ring
      _ <= 80 + 16 * Real.log (A / b) / (n : Real) := by norm_num
  · have hterm : 0 <= 16 * Real.log (A / b) / (n : Real) :=
      div_nonneg (mul_nonneg (by norm_num) hlog) hn0.le
    norm_num
    linarith

#print axioms logarithmicAdaptiveRadiusQ_sq
#print axioms two_le_logarithmicAdaptiveRadiusQ
#print axioms logarithmicAdaptiveRadiusQ_tailFits
#print axioms max_eight_two_logarithmicAdaptiveRadiusQ_sq_le

end Ttc.CVAdaptive
