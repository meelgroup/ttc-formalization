/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Nonconv
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Repairing `lem:nonconv`

`Ttc.Nonconv` records that the paper's upper-bound chain for `lem:nonconv`
invokes `Q ⊆ Q''`, whereas the actual containment is `Q'' ⊆ Q`.
What the stated `claim:cl` gives is a bound on `vol Q''`; transferring it to `vol Q`
costs the `claim:helper` factor `K = (1+θ/4)/(1−θ/4)` via `Q ⊆ Q' ⊆ k·Q''`.

**The repair.** Run the whole construction with internal parameter `θ = η/2` —
that is, compute `κ` and the required inscribed radius `γ` at `η/2` instead of at
`η` — and the paper's *stated* conclusion

  `vol Q ∈ [(1−η)|Q ∩ ℤⁿ|, (1+η)|Q ∩ ℤⁿ|]`

holds verbatim, `K` and all. This is `Ttc.nonconv_repaired`, proved below.

**The cost is at most one decimal digit of precision.** Halving the internal
parameter inflates the required radius from
`γ(η) = (16n/η)√(log(4r/η))` to `γ(η/2) = (32n/η)√(log(8r/η))`, and
`γ(η/2) ≤ 3·γ(η)` (`Ttc.gamma_half_le`). Since `GetPrecision` returns
`⌈log₁₀(γ/γ̂)⌉` and `log₁₀ 3 < 1`, the precision parameter `ρ` grows by at most
one (`Ttc.precision_increase_le_one`).

## Concretely, what to change in the paper

* **Algorithm 2 (`GetPrecision`), the line `γ ← (16n/η)√(log(4r/η))`:** replace by
  `γ ← (32n/η)√(log(8r/η))`.
* **`lem:nonconv`'s hypothesis:** require each `Pᵢ` to contain a ball of radius at least
  `(32n/η)√(log(8r/η))`. The separate common-centre gap (finding 2) is handled in
  `Ttc.Recentred`, which removes it rather than assuming it away.
* **`lem:nonconv`'s proof, upper bound:** replace "the last inequality follows from
  `Q ⊆ Q''`" by the two steps
  `vol Q'' ≤ |Q∩ℤⁿ|/(1−η/4)` and `vol Q ≤ vol Q' ≤ k^n·vol Q''`,
  then combine with `claim:helper` at `η/2`.
* Nothing downstream changes: `lem:lattice`, `lem:numlattice` and `thm:volumettc` are stated in terms
  of `lem:nonconv`'s conclusion, which is now restored exactly.
-/

namespace Ttc

/-! ## The two arithmetic facts the repair needs -/

/-- Upper half of the repair: with internal parameter `θ = η/2`, the `claim:helper`
factor and the `1/(1−θ/2)` loss together still fit inside `1 + η`. -/
theorem repair_upper_arith {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    1 + η / 8 ≤ (1 + η) * ((1 - η / 8) * (1 - η / 4)) := by
  nlinarith [sq_nonneg η, sq_nonneg (1 - η)]

/-- Lower half of the repair: with internal parameter `θ = η/2`, the lower bound
still clears `1 − η`. -/
theorem repair_lower_arith {η : ℝ} (h0 : 0 < η) (_h1 : η ≤ 1) :
    (1 - η) * (1 + η / 8) ≤ (1 - η / 8) * (1 - η / 4) := by
  nlinarith [sq_nonneg η]

/-! ## `lem:nonconv`, repaired

The hypotheses below are exactly `claim:cl` and `claim:helper` **instantiated at
`θ = η/2`**: `hA` is `claim:cl`(a) summed, `hBC` is `claim:cl`(b)+(c) summed, and `hK`
is the geometric input `vol Q' ≤ kⁿ·vol Q''` with `kⁿ ≤ (1+θ/4)/(1−θ/4)`. The
conclusion is the paper's statement of `lem:nonconv`, unchanged.
-/

/-- **`lem:nonconv`, repaired.**

Running the construction at internal parameter `θ = η/2` recovers the paper's
stated two-sided bound `vol Q ∈ [(1−η)N, (1+η)N]` — including the upper bound,
whose original proof used the containment `Q ⊆ Q''` in the wrong direction. -/
theorem nonconv_repaired {η N volQ volQ' volQ'' : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : 0 ≤ N)
    (hA : (1 - η / 4) * N ≤ volQ')
    (hBC : (1 - η / 4) * volQ'' ≤ N)
    (hK : volQ' ≤ ((1 + η / 8) / (1 - η / 8)) * volQ'')
    (hsub : volQ'' ≤ volQ) (hsup : volQ ≤ volQ') :
    (1 - η) * N ≤ volQ ∧ volQ ≤ (1 + η) * N := by
  have hB : (0:ℝ) < 1 - η / 8 := by linarith
  have hAp : (0:ℝ) < 1 + η / 8 := by linarith
  have hD : (0:ℝ) < 1 - η / 4 := by linarith
  have hne : (1:ℝ) - η / 8 ≠ 0 := ne_of_gt hB
  have h8 : (8:ℝ) - η ≠ 0 := by intro h; linarith
  -- clear the denominator in `hK`
  have hKcl : (1 - η / 8) * volQ' ≤ (1 + η / 8) * volQ'' := by
    have h := mul_le_mul_of_nonneg_left hK hB.le
    rwa [show (1 - η / 8) * (((1 + η / 8) / (1 - η / 8)) * volQ'') = (1 + η / 8) * volQ'' by
      field_simp] at h
  constructor
  · -- `A(1−η)N ≤ B(1−η/4)N ≤ B·volQ' ≤ A·volQ'' ≤ A·volQ`, with `A = 1+η/8`, `B = 1−η/8`
    have harith := repair_lower_arith hη hη1
    nlinarith [mul_le_mul_of_nonneg_right harith hN,
      mul_le_mul_of_nonneg_left hA hB.le,
      mul_le_mul_of_nonneg_left hsub hAp.le]
  · -- `(1−η/4)·volQ ≤ ... ≤ K·N`, then `repair_upper_arith`
    have hupp : (1 - η / 8) * ((1 - η / 4) * volQ) ≤ (1 + η / 8) * N := by
      calc (1 - η / 8) * ((1 - η / 4) * volQ)
          = (1 - η / 4) * ((1 - η / 8) * volQ) := by ring
        _ ≤ (1 - η / 4) * ((1 - η / 8) * volQ') :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsup hB.le) hD.le
        _ ≤ (1 - η / 4) * ((1 + η / 8) * volQ'') :=
            mul_le_mul_of_nonneg_left hKcl hD.le
        _ = (1 + η / 8) * ((1 - η / 4) * volQ'') := by ring
        _ ≤ (1 + η / 8) * N := mul_le_mul_of_nonneg_left hBC hAp.le
    have harith := repair_upper_arith hη hη1
    nlinarith [mul_le_mul_of_nonneg_right harith hN]

/-! ## The cost of the repair -/

/-- **The required inscribed radius grows by less than a factor `3`.**

`γ(θ) = (16n/θ)·√(log(4r/θ))`, so `γ(η/2) = (32n/η)·√(log(8r/η))`. -/
theorem gamma_half_le {η r : ℝ} {n : ℕ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r) :
    (32 * n / η) * Real.sqrt (Real.log (8 * r / η))
      ≤ 3 * ((16 * n / η) * Real.sqrt (Real.log (4 * r / η))) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `log (8r/η) = log (4r/η) + log 2`
  have hsplit : Real.log (8 * r / η) = Real.log (4 * r / η) + Real.log 2 := by
    rw [show (8:ℝ) * r / η = (4 * r / η) * 2 by ring,
      Real.log_mul (by positivity) (by norm_num)]
  -- `log (4r/η) ≥ log 4 = 2 log 2`
  have hL : 2 * Real.log 2 ≤ Real.log (4 * r / η) := by
    have h4 : Real.log 4 ≤ Real.log (4 * r / η) := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hη]; nlinarith
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hLpos : 0 < Real.log (4 * r / η) := by linarith
  -- `√(L + log 2) ≤ (3/2)·√L`
  have hsqrt : Real.sqrt (Real.log (8 * r / η)) ≤ 3 / 2 * Real.sqrt (Real.log (4 * r / η)) := by
    have hstep : Real.log (8 * r / η) ≤ 9 / 4 * Real.log (4 * r / η) := by
      rw [hsplit]; linarith
    have hrw : Real.sqrt (9 / 4 * Real.log (4 * r / η))
        = 3 / 2 * Real.sqrt (Real.log (4 * r / η)) := by
      rw [show (9:ℝ) / 4 = (3 / 2) ^ 2 by norm_num, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3 / 2)]
    calc Real.sqrt (Real.log (8 * r / η))
        ≤ Real.sqrt (9 / 4 * Real.log (4 * r / η)) := Real.sqrt_le_sqrt hstep
      _ = 3 / 2 * Real.sqrt (Real.log (4 * r / η)) := hrw
  have hcoef : (0:ℝ) ≤ 32 * n / η := by positivity
  calc (32 * n / η) * Real.sqrt (Real.log (8 * r / η))
      ≤ (32 * n / η) * (3 / 2 * Real.sqrt (Real.log (4 * r / η))) :=
        mul_le_mul_of_nonneg_left hsqrt hcoef
    _ = 3 * ((16 * n / η) * Real.sqrt (Real.log (4 * r / η))) := by ring

/-- **`GetPrecision` loses at most one decimal digit.**

`GetPrecision` returns `⌈log₁₀(γ/γ̂)⌉`. Replacing `γ` by anything at most `3γ`
raises that by at most `1`, because `log₁₀ 3 < 1`. -/
theorem precision_increase_le_one {ratio : ℝ} (h : 0 < ratio) :
    ⌈Real.logb 10 (3 * ratio)⌉ ≤ ⌈Real.logb 10 ratio⌉ + 1 := by
  have h3 : Real.logb 10 (3 * ratio) = Real.logb 10 3 + Real.logb 10 ratio := by
    rw [Real.logb, Real.logb, Real.logb, Real.log_mul (by norm_num) (ne_of_gt h)]
    ring
  have hlt : Real.logb 10 3 ≤ 1 := by
    have h10 : Real.logb 10 10 = 1 := Real.logb_self_eq_one (by norm_num)
    rw [← h10]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
  rw [h3]
  refine Int.ceil_le.2 ?_
  push_cast
  linarith [Int.le_ceil (Real.logb 10 ratio)]

end Ttc
