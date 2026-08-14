import Ttc.Volume.CVLogarithmicAdjustableRadius
import Ttc.Exec.CVHotRefreshHonestRuntime

/-!
# A radius-four logarithmic selector for a whole CV run

For `A ≥ 1` total sampler calls, the radius

`Q² = 16 + 4 log (20 A) / n`

is at least four and spends at most `1/20` total Gaussian truncation mass.  The
larger constant term (compared with `logarithmicAdaptiveRadiusQ`) is useful for the
operational radius-`Q` schedule: it makes `max 8 (2*Q) = 2*Q` definitionally
available after one elementary inequality, while retaining logarithmic growth.
-/

set_option autoImplicit false

namespace Ttc.CVGlobalLogarithmicRadius

open Arlib.GaussianCooling
open Ttc.CVAdaptive
open Ttc.CVHotRefreshHonestRuntime

/-- One truncation radius shared by all `A` calls of an estimator run. -/
noncomputable def globalLogarithmicRadiusQ (n : Nat) (A : Real) : Real :=
  Real.sqrt (16 + 4 * Real.log (20 * A) / (n : Real))

theorem globalLogarithmicRadiusQ_sq
    {n : Nat} (hn : 1 ≤ n) {A : Real} (hA : 1 ≤ A) :
    globalLogarithmicRadiusQ n A ^ 2 =
      16 + 4 * Real.log (20 * A) / (n : Real) := by
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hlog : 0 ≤ Real.log (20 * A) := by
    apply Real.log_nonneg
    nlinarith
  unfold globalLogarithmicRadiusQ
  exact Real.sq_sqrt (by positivity)

theorem four_le_globalLogarithmicRadiusQ
    {n : Nat} (hn : 1 ≤ n) {A : Real} (hA : 1 ≤ A) :
    4 ≤ globalLogarithmicRadiusQ n A := by
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hlog : 0 ≤ Real.log (20 * A) := by
    apply Real.log_nonneg
    nlinarith
  have hradicand : (16 : Real) ≤
      16 + 4 * Real.log (20 * A) / (n : Real) := by
    exact le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by norm_num) hlog) hn0.le)
  have hsqrt16 : Real.sqrt (16 : Real) = 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 16),
      Real.sqrt_nonneg (16 : Real)]
  rw [← hsqrt16, globalLogarithmicRadiusQ]
  exact Real.sqrt_le_sqrt hradicand

/-- The Gaussian radial-tail base at the global radius is bounded by the exact
exponential whose `n`th power is `1/(20A)`. -/
theorem globalLogarithmicRadiusQ_tailBase_le
    {n : Nat} (hn : 1 ≤ n) {A : Real} (hA : 1 ≤ A) :
    globalLogarithmicRadiusQ n A *
        Real.exp (-(globalLogarithmicRadiusQ n A ^ 2 - 1) / 2) ≤
      Real.exp (-Real.log (20 * A) / (n : Real)) := by
  let q := globalLogarithmicRadiusQ n A
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hq4 : 4 ≤ q := four_le_globalLogarithmicRadiusQ hn hA
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq4
  have hq2 : q ^ 2 = 16 + 4 * Real.log (20 * A) / (n : Real) :=
    globalLogarithmicRadiusQ_sq hn hA
  have hlogq0 := Real.log_le_sub_one_of_pos hq0
  have hquad : q - 1 ≤ q ^ 2 / 4 := by
    nlinarith [sq_nonneg (q - 2)]
  have hlogq : Real.log q ≤ q ^ 2 / 4 := hlogq0.trans hquad
  have hquarter : q ^ 2 / 4 =
      4 + Real.log (20 * A) / (n : Real) := by rw [hq2]; ring
  have hexponent :
      Real.log q - (q ^ 2 - 1) / 2 ≤
        -Real.log (20 * A) / (n : Real) := by
    calc
      Real.log q - (q ^ 2 - 1) / 2 ≤
          q ^ 2 / 4 - (q ^ 2 - 1) / 2 := sub_le_sub_right hlogq _
      _ = 1 / 2 - q ^ 2 / 4 := by ring
      _ = -(7 / 2 : Real) - Real.log (20 * A) / (n : Real) := by
        rw [hquarter]
        ring
      _ ≤ -Real.log (20 * A) / (n : Real) := by
        rw [show -(7 / 2 : Real) - Real.log (20 * A) / (n : Real) =
          -Real.log (20 * A) / (n : Real) - 7 / 2 by ring]
        exact sub_le_self _ (by norm_num)
  change q * Real.exp (-(q ^ 2 - 1) / 2) ≤ _
  calc
    q * Real.exp (-(q ^ 2 - 1) / 2) =
        Real.exp (Real.log q - (q ^ 2 - 1) / 2) := by
      rw [show -(q ^ 2 - 1) / 2 = -((q ^ 2 - 1) / 2) by ring,
        Real.exp_neg, Real.exp_sub, Real.exp_log hq0]
      simp only [div_eq_mul_inv]
    _ ≤ Real.exp (-Real.log (20 * A) / (n : Real)) :=
      Real.exp_le_exp.mpr hexponent

/-- A single global radius spends at most `1/20` across all `A` calls. -/
theorem globalLogarithmicRadiusQ_totalTail_le
    {n : Nat} (hn : 1 ≤ n) {A : Real} (hA : 1 ≤ A) :
    A * (globalLogarithmicRadiusQ n A *
        Real.exp (-(globalLogarithmicRadiusQ n A ^ 2 - 1) / 2)) ^ n ≤
      1 / 20 := by
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let q := globalLogarithmicRadiusQ n A
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num)
    (four_le_globalLogarithmicRadiusQ hn hA)
  have hbase := globalLogarithmicRadiusQ_tailBase_le hn hA
  have hbase0 : 0 ≤ q * Real.exp (-(q ^ 2 - 1) / 2) :=
    mul_nonneg hq0.le (Real.exp_pos _).le
  have hpow :
      (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n ≤
        Real.exp (-Real.log (20 * A) / (n : Real)) ^ n :=
    pow_le_pow_left₀ hbase0 hbase n
  have hexppow :
      Real.exp (-Real.log (20 * A) / (n : Real)) ^ n = 1 / (20 * A) := by
    rw [← Real.exp_nat_mul]
    have hnne : (n : Real) ≠ 0 := ne_of_gt hn0
    rw [show (n : Real) * (-Real.log (20 * A) / (n : Real)) =
        -Real.log (20 * A) by field_simp]
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 20 * A)]
    simp only [one_div]
  change A * (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n ≤ _
  calc
    A * (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n ≤
        A * Real.exp (-Real.log (20 * A) / (n : Real)) ^ n := by gcongr
    _ = A * (1 / (20 * A)) := by rw [hexppow]
    _ = 1 / 20 := by field_simp

/-- The exact sampler interface predicate for the same runwise tail budget. -/
theorem globalLogarithmicRadiusQ_tailFits
    {n : Nat} (hn : 1 ≤ n) {A : Real} (hA : 1 ≤ A) :
    AdjustableRadiusTailFits n A (1 / 20) (globalLogarithmicRadiusQ n A) := by
  constructor
  · exact lt_of_lt_of_le (by norm_num : (1 : Real) < 4)
      (four_le_globalLogarithmicRadiusQ hn hA)
  · exact globalLogarithmicRadiusQ_totalTail_le hn hA

/-- Since `Q ≥ 4`, the conductance denominator has no remaining maximum branch. -/
theorem max_eight_two_globalLogarithmicRadiusQ_sq
    {n : Nat} (hn : 1 ≤ n) {A : Real} (hA : 1 ≤ A) :
    max 8 (2 * globalLogarithmicRadiusQ n A) ^ 2 =
      64 + 16 * Real.log (20 * A) / (n : Real) := by
  have hq4 := four_le_globalLogarithmicRadiusQ hn hA
  rw [max_eq_right (by linarith), mul_pow,
    globalLogarithmicRadiusQ_sq hn hA]
  ring

/-- Cold phases (`sigmaSq ≤ 2`) have an `O(n^3 (1+log(20A)))` step coefficient. -/
theorem hotCappedStepCoefficient_globalQ_cold_le
    {n : Nat} (hn : 1 ≤ n) {A sigmaSq : Real}
    (hA : 1 ≤ A) (_hsigma0 : 0 ≤ sigmaSq) (hsigma2 : sigmaSq ≤ 2) :
    hotCappedStepCoefficient n (globalLogarithmicRadiusQ n A) sigmaSq ≤
      (72 + 16 * Real.log (20 * A)) * (n : Real) ^ 3 := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (20 * A) := Real.log_nonneg (by nlinarith)
  rw [hotCappedStepCoefficient,
    max_eight_two_globalLogarithmicRadiusQ_sq hn hA]
  have hn0 : (0 : Real) < n := by positivity
  field_simp
  nlinarith [mul_nonneg hlog (sq_nonneg ((n : Real) - 1)),
    mul_nonneg _hsigma0 (sq_nonneg (n : Real))]

/-- Hot phases bounded by `N` retain linear dependence on the variance/radial scale. -/
theorem hotCappedStepCoefficient_globalQ_hot_le
    {n : Nat} (hn : 1 ≤ n) {A sigmaSq N : Real}
    (hA : 1 ≤ A) (_hsigma0 : 0 ≤ sigmaSq) (hsigmaN : sigmaSq ≤ N) :
    hotCappedStepCoefficient n (globalLogarithmicRadiusQ n A) sigmaSq ≤
      (64 + 16 * Real.log (20 * A) + 4 * N) * (n : Real) ^ 3 := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (20 * A) := Real.log_nonneg (by nlinarith)
  rw [hotCappedStepCoefficient,
    max_eight_two_globalLogarithmicRadiusQ_sq hn hA]
  have hn0 : (0 : Real) < n := by positivity
  field_simp
  nlinarith [mul_nonneg hlog (sq_nonneg ((n : Real) - 1)),
    mul_nonneg _hsigma0 (sq_nonneg (n : Real))]

/-- Literal step size used by the operational kernel with the run-global radius. -/
noncomputable def globalLogarithmicDelta
    (n : Nat) (A sigmaSq : Real) : Real :=
  min (Real.sqrt sigmaSq /
      (max 8 (2 * globalLogarithmicRadiusQ n A) * Real.sqrt n))
    (1 / (2 * (n : Real)))

theorem globalLogarithmicDelta_pos
    {n : Nat} (hn : 1 ≤ n) {A sigmaSq : Real}
    (hA : 1 ≤ A) (hsigma : 0 < sigmaSq) :
    0 < globalLogarithmicDelta n A sigmaSq := by
  unfold globalLogarithmicDelta
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hq0 : 0 < globalLogarithmicRadiusQ n A :=
    lt_of_lt_of_le (by norm_num) (four_le_globalLogarithmicRadiusQ hn hA)
  exact lt_min
    (div_pos (Real.sqrt_pos.2 hsigma) (by positivity))
    (by positivity)

/-- Direct cold-phase coefficient bound for the literal operational step size. -/
theorem sigmaSq_mul_n_div_globalDelta_sq_cold_le
    {n : Nat} (hn : 1 ≤ n) {A sigmaSq : Real}
    (hA : 1 ≤ A) (hsigma : 0 < sigmaSq) (hsigma2 : sigmaSq ≤ 2) :
    sigmaSq * (n : Real) / globalLogarithmicDelta n A sigmaSq ^ 2 ≤
      (72 + 16 * Real.log (20 * A)) * (n : Real) ^ 3 := by
  calc
    _ ≤ hotCappedStepCoefficient n (globalLogarithmicRadiusQ n A) sigmaSq := by
      simpa only [globalLogarithmicDelta] using
        (sigmaSq_mul_n_div_adaptiveTerminalDeltaQ_sq_le hn
          (q := globalLogarithmicRadiusQ n A) hsigma)
    _ ≤ _ := hotCappedStepCoefficient_globalQ_cold_le
      hn hA hsigma.le hsigma2

/-- Direct hot-phase coefficient bound for the literal operational step size; the
variance scale remains linear, while the global-call dependence is logarithmic. -/
theorem sigmaSq_mul_n_div_globalDelta_sq_hot_le
    {n : Nat} (hn : 1 ≤ n) {A sigmaSq N : Real}
    (hA : 1 ≤ A) (hsigma : 0 < sigmaSq) (hsigmaN : sigmaSq ≤ N) :
    sigmaSq * (n : Real) / globalLogarithmicDelta n A sigmaSq ^ 2 ≤
      (64 + 16 * Real.log (20 * A) + 4 * N) * (n : Real) ^ 3 := by
  calc
    _ ≤ hotCappedStepCoefficient n (globalLogarithmicRadiusQ n A) sigmaSq := by
      simpa only [globalLogarithmicDelta] using
        (sigmaSq_mul_n_div_adaptiveTerminalDeltaQ_sq_le hn
          (q := globalLogarithmicRadiusQ n A) hsigma)
    _ ≤ _ := hotCappedStepCoefficient_globalQ_hot_le
      hn hA hsigma.le hsigmaN

#print axioms globalLogarithmicRadiusQ_totalTail_le
#print axioms globalLogarithmicRadiusQ_tailFits
#print axioms hotCappedStepCoefficient_globalQ_cold_le
#print axioms hotCappedStepCoefficient_globalQ_hot_le
#print axioms sigmaSq_mul_n_div_globalDelta_sq_cold_le
#print axioms sigmaSq_mul_n_div_globalDelta_sq_hot_le

end Ttc.CVGlobalLogarithmicRadius
