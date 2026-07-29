/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Geometry

/-!
# `lem:nonconv`: lattice points versus volume for a union of polytopes

The paper's `lem:nonconv` states, for `Q = ⋃ᵢ Pᵢ` with every `Pᵢ` containing an
`ℓ₂`-ball of radius `γ = (16n/η)√(log(4r/η))`,

  `vol Q ∈ [(1−η)·|Q ∩ ℤⁿ|, (1+η)·|Q ∩ ℤⁿ|]`.

Its proof consumes `claim:cl` — three statements about the randomized
rounding `rnd` of a uniform point — via two *summed* consequences, and `claim:helper`
via the volume ratio `vol Q' ≤ ((1+η/4)/(1−η/4)) · vol Q''`.

This file proves the summation steps and the whole deductive skeleton. `claim:cl`
itself (an Azuma/martingale argument about `rnd`) is **not** proved here: it is
taken as the two summed hypotheses `hA` and `hBC` below, which is exactly the
interface the paper's proof uses. See the module `Ttc.Analysis` for how this is
packaged, and the README for the precise proved/assumed split.

## Bug-oracle finding: the upper bound does not follow as written

The paper's upper-bound chain reads

  `1 − η/2 ≤ ∑_{x ∈ Q∩ℤⁿ} Pr[rnd p = x] ≤ ∑_{x} 1/vol Q'' ≤ |Q∩ℤⁿ|/vol Q`,
  "the last inequality follows from `Q ⊆ Q''`".

But `Q''` is the family *deflated* by `κ‖A_ij‖`, so `Q'' ⊆ Q`, not `Q ⊆ Q''`; and
`|Q∩ℤⁿ|/vol Q'' ≤ |Q∩ℤⁿ|/vol Q` needs `vol Q ≤ vol Q''`, i.e. the containment in
the direction that fails. What the stated claims *do* give is
`vol Q'' ≤ (1+η)|Q∩ℤⁿ|` (`Ttc.nonconv_upper_deflated`). Recovering a bound on
`vol Q` costs the extra factor `(1+η/4)/(1−η/4)` from `claim:helper`, via
`Q ⊆ Q' ⊆ k·Q''` (`Ttc.nonconv_upper_repaired`).

The lower bound is unaffected: it uses `Q'' ⊆ Q`, the correct direction, and is
proved here in the paper's own form (`Ttc.nonconv_lower`).

The defect is a constant-factor one — rerunning the argument with a smaller
internal `η` restores the stated form — so `thm:volumettc` survives, but the constants
in `GetPrecision` change. We record both the literal and the repaired statement.
-/

namespace Ttc

open Finset

/-! ## From `claim:cl` to its summed forms -/

/-- **Summation step for `claim:cl`(a).** If each of the `|T|` lattice points is hit
by the rounding with probability at least `(1 − η/2)/volQ'`, and the total
probability is at most `1`, then `(1 − η/2)·|T| ≤ volQ'`.

This is the paper's display `1 ≥ ∑_{x ∈ Q∩ℤⁿ} Pr[rnd p = x] ≥ (1−η/2)|Q∩ℤⁿ|/vol Q'`. -/
theorem sum_lower_of_claim_a {α : Type*} [DecidableEq α] {η volQ' : ℝ} (hvol : 0 < volQ')
    (T : Finset α) (pr : α → ℝ)
    (hpr : ∀ x ∈ T, (1 - η / 2) / volQ' ≤ pr x)
    (htot : ∑ x ∈ T, pr x ≤ 1) :
    (1 - η / 2) * T.card ≤ volQ' := by
  have hsum : (T.card : ℝ) * ((1 - η / 2) / volQ') ≤ ∑ x ∈ T, pr x := by
    calc (T.card : ℝ) * ((1 - η / 2) / volQ')
        = ∑ _x ∈ T, (1 - η / 2) / volQ' := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ T, pr x := sum_le_sum hpr
  have h : (T.card : ℝ) * ((1 - η / 2) / volQ') ≤ 1 := le_trans hsum htot
  rw [mul_div_assoc'] at h
  rw [div_le_one hvol] at h
  linarith

/-- **Summation step for `claim:cl`(b)+(c).** If the rounding lands in `Q` with
probability at least `1 − η/2`, and each individual lattice point is hit with
probability at most `1/volQ''`, then `(1 − η/2)·volQ'' ≤ |T|`.

This is the paper's display `1 − η/2 ≤ ∑_{x ∈ Q∩ℤⁿ} Pr[rnd p = x] ≤ |Q∩ℤⁿ|/vol Q''`. -/
theorem sum_upper_of_claim_bc {α : Type*} [DecidableEq α] {η volQ'' : ℝ} (hvol : 0 < volQ'')
    (T : Finset α) (pr : α → ℝ)
    (hb : 1 - η / 2 ≤ ∑ x ∈ T, pr x)
    (hc : ∀ x ∈ T, pr x ≤ 1 / volQ'') :
    (1 - η / 2) * volQ'' ≤ T.card := by
  have hsum : ∑ x ∈ T, pr x ≤ (T.card : ℝ) * (1 / volQ'') := by
    calc ∑ x ∈ T, pr x ≤ ∑ _x ∈ T, (1 / volQ'') := sum_le_sum hc
      _ = (T.card : ℝ) * (1 / volQ'') := by rw [sum_const, nsmul_eq_mul]
  have h : 1 - η / 2 ≤ (T.card : ℝ) * (1 / volQ'') := le_trans hb hsum
  rw [mul_one_div, le_div_iff₀ hvol] at h
  linarith

/-! ## The deductive skeleton of `lem:nonconv`

`N` stands for `|Q ∩ ℤⁿ|`, `volQ`, `volQ'`, `volQ''` for the volumes of the body,
its inflation and its deflation. The hypotheses `hA` and `hBC` are exactly the
outputs of the two summation lemmas above; `hK` is the `claim:helper` / geometry input
proved in `Ttc.Geometry`.
-/

/-- **Lower bound of `lem:nonconv`** — the paper's argument, in full.

From `(1−η/2)N ≤ vol Q'`, `vol Q' ≤ K · vol Q''` with `K = (1+η/4)/(1−η/4)`, and
`vol Q'' ≤ vol Q` (which holds since `Q'' ⊆ Q`), one gets `(1−η)N ≤ vol Q`. -/
theorem nonconv_lower {η N volQ volQ' volQ'' : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hA : (1 - η / 2) * N ≤ volQ')
    (hK : volQ' ≤ ((1 + η / 4) / (1 - η / 4)) * volQ'')
    (hsub : volQ'' ≤ volQ) (hN : 0 ≤ N) :
    (1 - η) * N ≤ volQ := by
  have hB : (0:ℝ) < 1 - η / 4 := by linarith
  have hAp : (0:ℝ) < 1 + η / 4 := by linarith
  have hne : (1:ℝ) - η / 4 ≠ 0 := ne_of_gt hB
  have h4 : (4:ℝ) - η ≠ 0 := by intro h; linarith
  -- clear the denominator in `hK`
  have hKcl : (1 - η / 4) * volQ' ≤ (1 + η / 4) * volQ'' := by
    have h := mul_le_mul_of_nonneg_left hK hB.le
    rwa [show (1 - η / 4) * (((1 + η / 4) / (1 - η / 4)) * volQ'') = (1 + η / 4) * volQ'' by
      field_simp] at h
  -- the cleared form of `nonconv_lower_arith`
  have harith : (1 + η / 4) * (1 - η) ≤ (1 - η / 4) * (1 - η / 2) := by nlinarith
  -- assemble: `A(1−η)N ≤ B(1−η/2)N ≤ B·volQ' ≤ A·volQ'' ≤ A·volQ`
  nlinarith [mul_le_mul_of_nonneg_right harith hN,
    mul_le_mul_of_nonneg_left hA hB.le,
    mul_le_mul_of_nonneg_left hsub hAp.le]

/-- **What the paper's upper-bound chain actually establishes**: a bound on the
volume of the *deflated* body `Q''`, not of `Q`. -/
theorem nonconv_upper_deflated {η N volQ'' : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : 0 ≤ N) (hBC : (1 - η / 2) * volQ'' ≤ N) :
    volQ'' ≤ (1 + η) * N := by
  have hden : (0:ℝ) < 1 - η / 2 := by linarith
  have h1 : volQ'' ≤ N / (1 - η / 2) := by
    rw [le_div_iff₀ hden]; linarith
  calc volQ'' ≤ N / (1 - η / 2) := h1
    _ = (1 - η / 2)⁻¹ * N := by rw [inv_mul_eq_div]
    _ ≤ (1 + η) * N :=
        mul_le_mul_of_nonneg_right (nonconv_upper_arith hη hη1) hN

/-- **Upper bound of `lem:nonconv`, repaired.** Since `Q ⊆ Q' ⊆ k·Q''`, the bound on
`vol Q''` transfers to `vol Q` at the cost of the `claim:helper` factor
`K = (1+η/4)/(1−η/4)`. For `0 < η ≤ 1` this gives `vol Q ≤ (5/3)(1+η)·N`; the
paper's stated `vol Q ≤ (1+η)·N` requires rerunning the construction with a
smaller internal `η`. -/
theorem nonconv_upper_repaired {η N volQ volQ' volQ'' : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : 0 ≤ N) (hBC : (1 - η / 2) * volQ'' ≤ N)
    (hsup : volQ ≤ volQ')
    (hK : volQ' ≤ ((1 + η / 4) / (1 - η / 4)) * volQ'') :
    volQ ≤ ((1 + η / 4) / (1 - η / 4)) * ((1 + η) * N) := by
  have hKpos : (0:ℝ) ≤ (1 + η / 4) / (1 - η / 4) := by
    apply le_of_lt; apply div_pos <;> linarith
  have hdef := nonconv_upper_deflated hη hη1 hN hBC
  calc volQ ≤ volQ' := hsup
    _ ≤ ((1 + η / 4) / (1 - η / 4)) * volQ'' := hK
    _ ≤ ((1 + η / 4) / (1 - η / 4)) * ((1 + η) * N) :=
        mul_le_mul_of_nonneg_left hdef hKpos

/-- The `claim:helper` factor is at most `5/3` on `0 < η ≤ 1`, so the repaired upper
bound of `lem:nonconv` loses at most a factor `5/3`. -/
theorem claim12_factor_le {η : ℝ} (_hη : 0 < η) (hη1 : η ≤ 1) :
    (1 + η / 4) / (1 - η / 4) ≤ 5 / 3 := by
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

end Ttc
