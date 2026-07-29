/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The arithmetic core: `claim:helper` and the ε-combination inequalities

This file proves, with no hypotheses beyond the stated ranges of the parameters,
every purely-arithmetic step of the paper's analysis:

* `Ttc.exp_two_mul_le_div` : `exp (2x) ≤ (1+x)/(1-x)` for `0 ≤ x ≤ 1/4`.
  (The paper's last step of `claim:helper`, "`exp(2x) ≤ (1+x)/(1-x)` for `0 < x < 1`".)
* `Ttc.claim_helper` : `claim:helper`, `kⁿ ≤ (1+η/4)/(1-η/4)`.
* `Ttc.lower_combine` / `Ttc.upper_combine` : the two inequalities that close the
  proof of `thm:volumettc`.
* `Ttc.nonconv_lower_arith` / `Ttc.nonconv_upper_arith` : the two inequalities
  that close the proof of `lem:nonconv`.

## Bug-oracle notes

* `claim:helper` is stated in the paper "for `n ∈ ℕ`", but its displayed expression
  `((n + η/8)/(n − η/8))ⁿ` is *negative inside the parentheses* when `n = 0`, and
  the intermediate step "since `η < n` we have `(η/8)/(n − η/8) ≤ 1`" silently
  assumes `n ≥ 1`. We therefore carry the hypothesis `1 ≤ n` explicitly. The
  restriction is harmless — `n` is the ambient dimension — but it is unstated.
* The final step of the paper's `claim:helper` chain asserts `exp(2x) ≤ (1+x)/(1−x)`
  "for `0 < x < 1`". That is true on the whole range, but the elementary
  third-order argument formalised here needs only `x ≤ 1/4`, which is all the
  claim uses (`x = η/4` with `η ≤ 1`).
-/

namespace Ttc

open Real

/-! ## A square-root superadditivity bound -/

/-- `√a + √b ≤ √(2(a+b))`, the quantitative form of the paper's
`√x + √y ≤ 2√((x+y)/2)`. -/
theorem sqrt_add_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a + Real.sqrt b ≤ Real.sqrt (2 * (a + b)) := by
  have hnn : 0 ≤ Real.sqrt a + Real.sqrt b := by positivity
  have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ 2 * (a + b) := by
    have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]
  calc Real.sqrt a + Real.sqrt b
      = Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (2 * (a + b)) := Real.sqrt_le_sqrt hsq

/-- The special case used in `claim:helper`: `√(2A) + √(2B) ≤ 2√(A+B)`. -/
theorem sqrt_two_mul_add_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (2 * A) + Real.sqrt (2 * B) ≤ 2 * Real.sqrt (A + B) := by
  have h := sqrt_add_sqrt_le (by linarith : (0:ℝ) ≤ 2 * A) (by linarith : (0:ℝ) ≤ 2 * B)
  have hrw : 2 * (2 * A + 2 * B) = (2 * Real.sqrt (A + B)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]; ring
  rw [hrw, Real.sqrt_sq (by positivity)] at h
  exact h

/-! ## The exponential bound -/

/-- `exp y ≤ 1 + y + y²/2 + (2/9)y³` for `0 ≤ y ≤ 1`, from Mathlib's `Real.exp_bound'`
at order 3. -/
theorem exp_le_cubic {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 + (2 / 9) * y ^ 3 := by
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- **The last step of `claim:helper`.** `exp (2x) ≤ (1+x)/(1-x)` for `0 ≤ x ≤ 1/4`.

The paper states this for `0 < x < 1`; the elementary proof here uses the
third-order Taylor bound, which suffices on the range actually needed. -/
theorem exp_two_mul_le_div {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) :
    Real.exp (2 * x) ≤ (1 + x) / (1 - x) := by
  have hden : (0:ℝ) < 1 - x := by linarith
  rw [le_div_iff₀ hden]
  have hb := exp_le_cubic (y := 2 * x) (by linarith) (by linarith)
  nlinarith [pow_nonneg h0 3, pow_nonneg h0 4, sq_nonneg x]

/-! ## `claim:helper` -/

/-- `(1 + u)ⁿ ≤ exp (n * u)` for `0 ≤ u`. -/
theorem one_add_pow_le_exp {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n ≤ Real.exp (n * u) := by
  have h : (1 + u) ^ n ≤ (Real.exp u) ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp u]) n
  calc (1 + u) ^ n ≤ (Real.exp u) ^ n := h
    _ = Real.exp (n * u) := by rw [← Real.exp_nat_mul]

/-- The core power bound of `claim:helper`, in cleared-denominator form:
`((8n + η)/(8n − η))ⁿ ≤ (1 + η/4)/(1 − η/4)` for `0 < η ≤ 1 ≤ n`. -/
theorem ratio_pow_le {η : ℝ} {n : ℕ} (hη : 0 < η) (hη1 : η ≤ 1) (hn : 1 ≤ n) :
    ((8 * n + η) / (8 * n - η)) ^ n ≤ (1 + η / 4) / (1 - η / 4) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hd : (0:ℝ) < 8 * n - η := by linarith
  -- rewrite the ratio as `1 + u`
  have hu : (8 * n + η) / (8 * n - η) = 1 + 2 * η / (8 * n - η) := by
    field_simp; ring
  have hu0 : (0:ℝ) ≤ 2 * η / (8 * n - η) := by positivity
  -- `n * u ≤ η/2`
  have hnu : (n : ℝ) * (2 * η / (8 * n - η)) ≤ η / 2 := by
    have hrw : (n : ℝ) * (2 * η / (8 * n - η)) = ((n : ℝ) * (2 * η)) / (8 * n - η) := by ring
    rw [hrw, div_le_iff₀ hd]
    nlinarith
  calc ((8 * n + η) / (8 * n - η)) ^ n
      = (1 + 2 * η / (8 * n - η)) ^ n := by rw [hu]
    _ ≤ Real.exp ((n : ℝ) * (2 * η / (8 * n - η))) := one_add_pow_le_exp hu0 n
    _ ≤ Real.exp (η / 2) := Real.exp_le_exp.2 hnu
    _ = Real.exp (2 * (η / 4)) := by ring_nf
    _ ≤ (1 + η / 4) / (1 - η / 4) := exp_two_mul_le_div (by linarith) (by linarith)

/-- Monotonicity of `t ↦ (γ + t)/(γ − t)` on `[0, γ)`. -/
theorem ratio_mono {γ s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < γ) :
    (γ + s) / (γ - s) ≤ (γ + t) / (γ - t) := by
  have h1 : (0:ℝ) < γ - t := by linarith
  have h2 : (0:ℝ) < γ - s := by linarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

/-- **`claim:helper`.**

With `r ≥ 1` the total facet count, `0 < η ≤ 1`, and `n ≥ 1` the dimension, set
`κ = √(2 log(4/η)) + √(2 log r)` and `γ = (16n/η)·√(log(4r/η))`. Then
`((γ + κ)/(γ − κ))ⁿ ≤ (1 + η/4)/(1 − η/4)`.

`γ` is exactly the inscribed-ball radius required by `lem:nonconv`, and `(γ+κ)/(γ−κ)`
is the paper's `k` evaluated at the extremal facet. -/
theorem claim_helper_of {η : ℝ} {n : ℕ} (hη : 0 < η) (hη1 : η ≤ 1) (hn : 1 ≤ n)
    {L κ : ℝ} (hL : 0 < L) (hκ0 : 0 ≤ κ) (hκle : κ ≤ 2 * Real.sqrt L) :
    (((16 * n / η) * Real.sqrt L + κ) / ((16 * n / η) * Real.sqrt L - κ)) ^ n
      ≤ (1 + η / 4) / (1 - η / 4) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hcpos : (16:ℝ) ≤ 16 * n / η := by rw [le_div_iff₀ hη]; nlinarith
  -- `2√L < γ`
  have hlt : 2 * Real.sqrt L < (16 * n / η) * Real.sqrt L :=
    mul_lt_mul_of_pos_right (by linarith) hsL
  -- monotonicity in the numerator perturbation
  have hmono := ratio_mono (γ := (16 * n / η) * Real.sqrt L) hκ0 hκle hlt
  -- the `√L` factors cancel, leaving `(8n+η)/(8n−η)`
  have hcancel : ((16 * n / η) * Real.sqrt L + 2 * Real.sqrt L) /
      ((16 * n / η) * Real.sqrt L - 2 * Real.sqrt L) = (8 * n + η) / (8 * n - η) := by
    rw [show (16 * (n:ℝ) / η) * Real.sqrt L + 2 * Real.sqrt L
          = (16 * n / η + 2) * Real.sqrt L by ring,
      show (16 * (n:ℝ) / η) * Real.sqrt L - 2 * Real.sqrt L
          = (16 * n / η - 2) * Real.sqrt L by ring,
      mul_div_mul_right _ _ (ne_of_gt hsL)]
    rw [div_eq_div_iff (by intro h; nlinarith) (by intro h; nlinarith)]
    field_simp
    ring
  rw [hcancel] at hmono
  refine le_trans (pow_le_pow_left₀ ?_ hmono n) (ratio_pow_le hη hη1 hn)
  have h2 : 0 < (16 * n / η) * Real.sqrt L - κ := by linarith
  positivity

/-- **`claim:helper`**, at the paper's concrete `κ` and `γ`. -/
theorem claim_helper {η r : ℝ} {n : ℕ} (hη : 0 < η) (hη1 : η ≤ 1) (hn : 1 ≤ n)
    (hr : 1 ≤ r) :
    (((16 * n / η) * Real.sqrt (Real.log (4 * r / η)) +
        (Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r))) /
      ((16 * n / η) * Real.sqrt (Real.log (4 * r / η)) -
        (Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r)))) ^ n
      ≤ (1 + η / 4) / (1 - η / 4) := by
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hlogη : 0 ≤ Real.log (4 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη]; linarith)
  have hsplit : Real.log (4 * r / η) = Real.log (4 / η) + Real.log r := by
    rw [show (4 : ℝ) * r / η = (4 / η) * r by ring,
      Real.log_mul (by positivity) (by linarith)]
  have hLpos : 0 < Real.log (4 * r / η) := by
    have h4 : Real.log 4 ≤ Real.log (4 / η) := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hη]; nlinarith
    have h4' : 0 < Real.log 4 := Real.log_pos (by norm_num)
    rw [hsplit]; linarith
  refine claim_helper_of hη hη1 hn hLpos (by positivity) ?_
  rw [hsplit]
  exact sqrt_two_mul_add_le hlogη hlogr


/-- **`(1 + α/n)ⁿ ≤ 1 + 2α` for `0 ≤ α ≤ 1`, `n ≥ 1`.**

The paper cites this as a "standard inequality" when passing from `κ/γ` to the
shell factor. It follows from `(1+u)ⁿ ≤ exp(nu)` and `exp α ≤ 1 + 2α` on `[0,1]`. -/
theorem one_add_div_pow_le {α : ℝ} {n : ℕ} (hn : 1 ≤ n) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (1 + α / n) ^ n ≤ 1 + 2 * α := by
  have hn0 : (0:ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have h := one_add_pow_le_exp (u := α / (n : ℝ)) (by positivity) n
  have hcancel : (n : ℝ) * (α / (n : ℝ)) = α := by field_simp
  rw [hcancel] at h
  have hexp : Real.exp α ≤ 1 + 2 * α := by
    have hb := exp_le_cubic h0 h1
    nlinarith [pow_nonneg h0 3, sq_nonneg α]
  linarith

/-! ## The ε-combination inequalities of `thm:volumettc` -/

/-- Lower half of the proof of `thm:volumettc`: `(1 − ε/3)/(1 + ε/8) ≥ 1 − ε`.

The paper's side condition `ε ≤ 1` turns out to be unnecessary here (the
inequality holds for every `ε > 0`); we keep the binder for correspondence with
the paper but do not use it. -/
theorem lower_combine {ε : ℝ} (h0 : 0 < ε) (_h1 : ε ≤ 1) :
    1 - ε ≤ (1 - ε / 3) / (1 + ε / 8) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Upper half of the proof of `thm:volumettc`: `(1 + ε/3)/(1 − ε/8) ≤ 1 + ε`. -/
theorem upper_combine {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (1 + ε / 3) / (1 - ε / 8) ≤ 1 + ε := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-! ## The η-combination inequalities of `lem:nonconv` -/

/-- Used for the upper bound of `lem:nonconv`: `(1 − η/2)⁻¹ ≤ 1 + η` for `0 < η ≤ 1`. -/
theorem nonconv_upper_arith {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    (1 - η / 2)⁻¹ ≤ 1 + η := by
  rw [inv_eq_one_div, div_le_iff₀ (by linarith : (0:ℝ) < 1 - η / 2)]
  nlinarith

/-- Used for the lower bound of `lem:nonconv`:
`((1 − η/4)/(1 + η/4)) * (1 − η/2) ≥ 1 − η` for `0 < η ≤ 1`.

As with `Ttc.lower_combine`, the constraint `η ≤ 1` is not actually needed. -/
theorem nonconv_lower_arith {η : ℝ} (h0 : 0 < η) (_h1 : η ≤ 1) :
    1 - η ≤ (1 - η / 4) / (1 + η / 4) * (1 - η / 2) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith

end Ttc
