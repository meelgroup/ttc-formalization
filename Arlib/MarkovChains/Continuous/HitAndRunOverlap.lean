/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.HitAndRunStep
import Arlib.Convexity.CrossRatio
import Arlib.Probability.TV
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 4.1 of Lovász–Vempala: two nearby points have overlapping one-step laws

This file proves the key lemma connecting geometry to probability for the hit-and-run walk:
if `u` and `v` are close *both* in the cross-ratio distance `d_K` *and* in the Euclidean
distance measured against the median step `F(u)`, then the two one-step distributions
`P_u`, `P_v` are **not** almost disjoint — their total variation distance is bounded away
from `1`.

Lovász–Vempala, *Hit-and-Run from a Corner* (SIAM J. Comput. 35 (2006) 985–1005), state it
as **Lemma 4.1** and attribute it, without proof, to

> L. Lovász, *Hit-and-run mixes fast*, Math. Programming Ser. A **86** (1999) 443–461,

where it is **Lemma 8** (p. 451–454).  Everything below follows that proof.  The source used
here is the author's PDF at `https://faculty.washington.edu/harin/L1.pdf`; the text was
re-extracted with the MathTime/`cmsy` font encodings resolved glyph-by-glyph, so the
relation symbols (`≤`, `≥`, `∈`, `=`, `+`, `[`, `]`) are read from the font's own encoding
vector and not guessed — the failure mode that produced a spurious "bug" report earlier in
this development.

## The shape of the argument

Fix a measurable `A ⊆ K`.  Lovász partitions `A` into four pieces and bounds `P_u` on the
first three:

* `A₁ = {x ∈ A : |x − u| < F(u)}`, with `P_u(A₁) ≤ 1/8` — this is *exactly* equation (4),
  the defining property of `F`;
* `A₂ = {x ∈ A : |⟨x − u, u − v⟩| > n^{-1/2}|x − u||u − v|}`, the steps whose direction is
  **not** almost orthogonal to `u − v`;
* `A₃ = {x ∈ A : |x − u| < (1/3)|u − a(u,x)|}`, the steps that stop close to `u` relative to
  the chord;
* `S = A \ A₁ \ A₂ \ A₃`.

On `S` the two densities of equation (5) are comparable, and one gets `P_v(S) ≥ c·P_u(S)`.
Summing, `P_u(A) − P_v(A) ≤ P_u(A) − c·P_u(S) ≤ 1 − c·(1 − q)` where `q` bounds
`P_u(A₁ ∪ A₂ ∪ A₃)`.

## What is proved here, and what is assumed

**Proved, with no extra hypothesis:**

* `Arlib.MarkovChains.norm_sub_le_of_almost_orthogonal` — the paper's (10),
  `|x − v| ≤ (1 + 4/n)|x − u|`, from (7) and (8).  Pure algebra in the inner product space.
* `Arlib.MarkovChains.hitAndRunDensity_ge_of_chordLength_le` — **the chord-density
  comparison, the crux**: from `ℓ(v,x)·|x − u| ≤ 2·|x − v|·ℓ(u,x)` and
  `|x − v| ≤ N·|x − u|`, the density of equation (5) satisfies
  `(2Nⁿ)⁻¹·hitAndRunDensity K u x ≤ hitAndRunDensity K v x`.
* `Arlib.MarkovChains.mul_hitAndRunProposal_le` — integrating that comparison against
  equation (5): `c·P_u(S) ≤ P_v(S)`.
* `Arlib.MarkovChains.pow_one_add_four_div_le_exp`, `two_mul_exp_four_lt` — `(1 + 4/n)ⁿ ≤ e⁴`
  and `2e⁴ < 120`, the paper's constant.
* `Arlib.MarkovChains.hitAndRun_ball_medianStep_le` — `P_u(A₁) ≤ 1/8`, from
  `Arlib.hitAndRun_closedBall_le_of_lt_medianStep` by exhausting the open ball.
* `Arlib.MarkovChains.tvLe_of_overlap` — the assembly: a setwise lower bound `c·μ ≤ ν` off a
  set of `μ`-mass `≤ q` gives `TVLe μ ν (1 − c(1 − q))`.
* `Arlib.MarkovChains.tvLe_hitAndRun_of_overlap` — the two combined, for the walk.

**Assumed, as inline hypotheses of the capstone `tvLe_hitAndRun_lemma41`** (no named `Prop`
is introduced for any of them; all three are *unproved* in this repository):

1. `hcap` — the spherical-cap estimate `P_u(A₂) ≤ q₂`.  This is the paper's "it takes a
   standard computation"; formally it is
   `σ_{n-1}{θ : |⟨θ, ŵ⟩| > n^{-1/2}} ≤ q₂`, an estimate on the distribution of one
   coordinate of a uniform point of `Sⁿ⁻¹`.  Mathlib v4.32 has neither that distribution
   nor the rotation invariance of `Measure.toSphere` that a symmetry proof would need — the
   same gap `Arlib/Convexity/HitAndRunStep.lean` already reports for `θ ↦ −θ`.  See the
   **constants** section below: the paper's value `1/6` for `q₂` is wrong.
2. `hchord` — the chord comparison `ℓ(v,x)·|x − u| ≤ 2·|x − v|·ℓ(u,x)`.  Lovász proves it
   by **Menelaus' theorem** applied to the triangle `u v x` and the transversal through
   `a(u,v)` and `a(v,x)`, using `d_K(u,v) < 1/8` and `|u − a(u,x)| ≤ 3|x − u|`.  Mathlib
   v4.32 has no Menelaus theorem and no chord-endpoint calculus for the ray
   parameterisation, so this is threaded rather than proved.
3. `hA3` — `P_u(A₃) ≤ 1/3`.  `A₃` is written here as `{x : chordLow K u x < −3}`, which is
   exactly `|u − a(u,x)| > 3|x − u|` in the chord coordinate of
   `Arlib/Convexity/CrossRatio.lean`.  The bound is the elementary "a sub-segment of the
   chord of length `ℓ/3`", but it needs the identification of `chordSet K u θ` with a
   closed interval and the behaviour of `chordLow` under the reparameterisation
   `x ↦ u + tθ`; not carried out here.

The capstone therefore proves the *implication* Lemma 4.1 rests on, with the three geometric
inputs named and visible in its type.  Nothing in this file is a definition that asserts an
unproved identity.

## Constants: the printed `1/6` is wrong, the printed `1 − 1/500` survives

Lovász's proof bounds the three bad pieces by `1/8`, `1/6` and `1/3`, rounds the sum up to
`3/4`, rounds `2e⁴ = 109.19…` up to `120`, and concludes `1 − 1/500`.

**The `1/6` is not correct.**  The paper defines `C` as the cap `{θ ∈ Sⁿ⁻¹ : ⟨θ, u − v⟩ ≥
n^{-1/2}|u − v|}` and says the probability in question is "the ratio between the surface of
`C` and the surface of the half-sphere", i.e. `2·σ(C) = σ{θ : |⟨θ, ŵ⟩| ≥ n^{-1/2}}`.  That
quantity is `1/2` at `n = 2`, `1 − 3^{-1/2} = 0.4226…` at `n = 3`, and decreases to
`2(1 − Φ(1)) = 0.31731…` as `n → ∞`.  It is **never** below `1/6 = 0.1666…`; the printed
value is off by about a factor of two, which is exactly the factor between a sphere and a
half-sphere.  (Even the one-sided `σ(C)` exceeds `1/6` for every `n ≤ 24` or so, so no
reading of the sentence makes `1/6` correct.)

**The conclusion `1 − 1/500` nevertheless holds** — but only if one keeps the sharp constant
`c = (2(1 + 4/n)ⁿ)⁻¹` instead of the printed rounding `1/120`.  With `q = 1/8 + q₂(n) + 1/3`
the proof yields `1 − c(1 − q)`, and `1/(c(1 − q))` is `432` at `n = 2`, `212` at `n = 4`,
and increases to `486.7…` as `n → ∞` — always below `500`, with about `2.7%` of slack.
With the paper's own rounded `1/120` one needs `q ≤ 0.76`, whereas `q → 0.7756…`: **the
printed chain `1/8 + 1/6 + 1/3 < 3/4` and `1/120` does not deliver `1 − 1/500`.**  Two
independent roundings-up therefore hide, and just barely absorb, one genuine error.

This file does not hard-code any of these numbers.  `tvLe_hitAndRun_lemma41` is parametric
in `q₂` and returns the sharp `1 − (1 − q)/(2(1 + 4/n)ⁿ)`, so a caller who can prove a cap
bound gets whatever constant that bound supports.  `tvLe_hitAndRun_lemma41_of_half` records
the dimension-free instance `q₂ = 1/2`, giving `1 − 1/2880` at the `1/120` rounding.
-/

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal RealInnerProductSpace

namespace Arlib.MarkovChains

open Arlib

variable {n : ℕ}

/-! ## The Euclidean estimate (10) -/

/-- **The paper's (10).**  If the step `x − u` is long compared with `u − v` (the paper's
(7), here `√n·|u − v| ≤ 2|x − u|`) and is almost orthogonal to `u − v` (the paper's (8),
here `√n·|⟨x − u, u − v⟩| ≤ |x − u|·|u − v|`), then `|x − v| ≤ (1 + 4/n)|x − u|`.

The two hypotheses give `|u − v|² ≤ (4/n)|x − u|²` and `2⟨x − u, u − v⟩ ≤ (4/n)|x − u|²`,
whence `|x − v|² ≤ (1 + 8/n)|x − u|² ≤ (1 + 4/n)²|x − u|²`. -/
theorem norm_sub_le_of_almost_orthogonal (hn : n ≠ 0)
    (u v x : EuclideanSpace ℝ (Fin n))
    (h7 : Real.sqrt n * ‖u - v‖ ≤ 2 * ‖x - u‖)
    (h8 : Real.sqrt n * |⟪x - u, u - v⟫| ≤ ‖x - u‖ * ‖u - v‖) :
    ‖x - v‖ ≤ (1 + 4 / (n : ℝ)) * ‖x - u‖ := by
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hs : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hxu : (0 : ℝ) ≤ ‖x - u‖ := norm_nonneg _
  have huv : (0 : ℝ) ≤ ‖u - v‖ := norm_nonneg _
  have hxv : (0 : ℝ) ≤ ‖x - v‖ := norm_nonneg _
  have hdecomp : x - v = (x - u) + (u - v) := by abel
  have hsq : ‖x - v‖ ^ 2
      = ‖x - u‖ ^ 2 + 2 * ⟪x - u, u - v⟫ + ‖u - v‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real]
  -- `2⟨x−u,u−v⟩ ≤ (4/n)|x−u|²`
  have hinner : ⟪x - u, u - v⟫ ≤ |⟪x - u, u - v⟫| := le_abs_self _
  have habs : Real.sqrt n * (Real.sqrt n * |⟪x - u, u - v⟫|)
      ≤ 2 * ‖x - u‖ * ‖x - u‖ := by
    calc Real.sqrt n * (Real.sqrt n * |⟪x - u, u - v⟫|)
        ≤ Real.sqrt n * (‖x - u‖ * ‖u - v‖) := by
          exact mul_le_mul_of_nonneg_left h8 hspos.le
      _ = ‖x - u‖ * (Real.sqrt n * ‖u - v‖) := by ring
      _ ≤ ‖x - u‖ * (2 * ‖x - u‖) := mul_le_mul_of_nonneg_left h7 hxu
      _ = 2 * ‖x - u‖ * ‖x - u‖ := by ring
  have hcross : (n : ℝ) * |⟪x - u, u - v⟫| ≤ 2 * ‖x - u‖ * ‖x - u‖ := by
    calc (n : ℝ) * |⟪x - u, u - v⟫|
        = Real.sqrt n * (Real.sqrt n * |⟪x - u, u - v⟫|) := by rw [← mul_assoc, hs]
      _ ≤ _ := habs
  -- `|u−v|² ≤ (4/n)|x−u|²`
  have hnormsq : (n : ℝ) * ‖u - v‖ ^ 2 ≤ 4 * ‖x - u‖ ^ 2 := by
    have hkey : (Real.sqrt n * ‖u - v‖) * (Real.sqrt n * ‖u - v‖)
        ≤ (2 * ‖x - u‖) * (2 * ‖x - u‖) :=
      mul_le_mul h7 h7 (by positivity) (by positivity)
    have hexp : (Real.sqrt n * ‖u - v‖) * (Real.sqrt n * ‖u - v‖)
        = (n : ℝ) * ‖u - v‖ ^ 2 := by
      rw [show (Real.sqrt n * ‖u - v‖) * (Real.sqrt n * ‖u - v‖)
          = (Real.sqrt n * Real.sqrt n) * ‖u - v‖ ^ 2 by ring, hs]
    have hexp2 : (2 * ‖x - u‖) * (2 * ‖x - u‖) = 4 * ‖x - u‖ ^ 2 := by ring
    linarith [hkey, hexp, hexp2]
  -- put the pieces together
  have hkey : ‖x - v‖ ^ 2 ≤ ((1 + 4 / (n : ℝ)) * ‖x - u‖) ^ 2 := by
    set d : ℝ := 4 / (n : ℝ) with hd
    set X : ℝ := ‖x - u‖ ^ 2 with hX
    have h1 : 2 * ⟪x - u, u - v⟫ ≤ d * X := by
      rw [hd, hX, div_mul_eq_mul_div, le_div_iff₀ hnR]
      nlinarith [hcross, mul_le_mul_of_nonneg_left hinner hnR.le]
    have h2 : ‖u - v‖ ^ 2 ≤ d * X := by
      rw [hd, hX, div_mul_eq_mul_div, le_div_iff₀ hnR]
      nlinarith [hnormsq]
    have hexp : ((1 + d) * ‖x - u‖) ^ 2 = X + 2 * (d * X) + d ^ 2 * X := by
      simp only [hX]; ring
    have hpos : 0 ≤ d ^ 2 * X := by rw [hX]; positivity
    rw [hsq, hexp]
    linarith
  nlinarith [hkey, hxv, mul_nonneg (by positivity : (0:ℝ) ≤ 1 + 4 / (n : ℝ)) hxu]

/-! ## `(1 + 4/n)ⁿ ≤ e⁴` -/

/-- `(1 + 4/n)ⁿ ≤ e⁴` for every `n`. -/
theorem pow_one_add_four_div_le_exp (n : ℕ) :
    (1 + 4 / (n : ℝ)) ^ n ≤ Real.exp 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero]
    nlinarith [Real.add_one_le_exp (4 : ℝ)]
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : (1 + 4 / (n : ℝ)) ≤ Real.exp (4 / (n : ℝ)) := by
      have := Real.add_one_le_exp (4 / (n : ℝ))
      linarith
    calc (1 + 4 / (n : ℝ)) ^ n ≤ (Real.exp (4 / (n : ℝ))) ^ n :=
          pow_le_pow_left₀ (by positivity) h1 n
      _ = Real.exp ((n : ℝ) * (4 / (n : ℝ))) := (Real.exp_nat_mul _ n).symm
      _ = Real.exp 4 := by rw [mul_div_cancel₀ _ hnR.ne']

/-- `2e⁴ < 120` — the paper's rounding of `2e⁴ = 109.19…`. -/
theorem two_mul_exp_four_lt : 2 * Real.exp 4 < 120 := by
  have h : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have : Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 := by
    exact pow_lt_pow_left₀ h1 h0.le (by norm_num)
  rw [h]
  nlinarith [this]

/-- `(2(1 + 4/n)ⁿ)⁻¹ ≥ 1/120`: the paper's constant `1/120` is a valid, if lossy,
substitute for the sharp `(2(1 + 4/n)ⁿ)⁻¹`. -/
theorem one_div_le_inv_two_mul_pow (n : ℕ) :
    (1 : ℝ) / 120 ≤ 1 / (2 * (1 + 4 / (n : ℝ)) ^ n) := by
  have hpos : (0 : ℝ) < (1 + 4 / (n : ℝ)) ^ n := by positivity
  have h := pow_one_add_four_div_le_exp n
  have h2 : 2 * (1 + 4 / (n : ℝ)) ^ n < 120 := by
    nlinarith [two_mul_exp_four_lt]
  exact one_div_le_one_div_of_le (by positivity) h2.le

/-! ## The chord-density comparison — the crux -/

/-- **The one-step density comparison of Lovász's proof.**

Given the two pointwise facts the paper establishes on `S`,

* the chord bound `ℓ(v,x)·|x − u| ≤ 2·|x − v|·ℓ(u,x)` (Menelaus, `hchord`), and
* the norm bound `|x − v| ≤ N·|x − u|` (the paper's (10), `hnorm`),

the integrand of equation (5) at `v` dominates `(2Nⁿ)⁻¹` times the integrand at `u`.

No convexity, measurability or boundedness is used: this is arithmetic in `ℝ≥0∞` on the
closed form `hitAndRunDensity K u x = (ℓ(u,x)·|x − u|^{n−1})⁻¹`. -/
theorem hitAndRunDensity_ge_of_chordLength_le (hn : n ≠ 0)
    {K : Set (EuclideanSpace ℝ (Fin n))} {u v x : EuclideanSpace ℝ (Fin n)}
    (hxu : x ≠ u) {N : ℝ} (hN : 0 < N)
    (hnorm : ‖x - v‖ ≤ N * ‖x - u‖)
    (hchord : chordLength K v x * ENNReal.ofReal ‖x - u‖
      ≤ 2 * (ENNReal.ofReal ‖x - v‖ * chordLength K u x)) :
    (ENNReal.ofReal (2 * N ^ n))⁻¹ * hitAndRunDensity K u x ≤ hitAndRunDensity K v x := by
  have hxu0 : (0 : ℝ) < ‖x - u‖ := by
    rw [norm_pos_iff, sub_ne_zero]; exact hxu
  have hcpos : (0 : ℝ) < 2 * N ^ n := by positivity
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * N ^ n) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hcpos
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  set A : ℝ≥0∞ := chordLength K u x * ENNReal.ofReal (‖x - u‖ ^ (n - 1)) with hA
  set B : ℝ≥0∞ := chordLength K v x * ENNReal.ofReal (‖x - v‖ ^ (n - 1)) with hB
  -- the key inequality `B ≤ c * A`
  have hn1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_ne_zero hn
  have hpow : ‖x - v‖ * ‖x - v‖ ^ (n - 1) = ‖x - v‖ ^ n := by
    rw [mul_comm, ← pow_succ, hn1]
  have hpowu : ‖x - u‖ ^ (n - 1) * ‖x - u‖ = ‖x - u‖ ^ n := by
    rw [← pow_succ, hn1]
  have hmain : B * ENNReal.ofReal ‖x - u‖ ≤ c * A * ENNReal.ofReal ‖x - u‖ := by
    have step1 : B * ENNReal.ofReal ‖x - u‖
        = (chordLength K v x * ENNReal.ofReal ‖x - u‖)
            * ENNReal.ofReal (‖x - v‖ ^ (n - 1)) := by
      rw [hB]; ring
    have step2 : (chordLength K v x * ENNReal.ofReal ‖x - u‖)
          * ENNReal.ofReal (‖x - v‖ ^ (n - 1))
        ≤ (2 * (ENNReal.ofReal ‖x - v‖ * chordLength K u x))
          * ENNReal.ofReal (‖x - v‖ ^ (n - 1)) :=
      mul_le_mul' hchord le_rfl
    have hprod : ENNReal.ofReal ‖x - v‖ * ENNReal.ofReal (‖x - v‖ ^ (n - 1))
        = ENNReal.ofReal (‖x - v‖ ^ n) := by
      rw [← ENNReal.ofReal_mul (norm_nonneg _), hpow]
    have step3 : (2 * (ENNReal.ofReal ‖x - v‖ * chordLength K u x))
          * ENNReal.ofReal (‖x - v‖ ^ (n - 1))
        = 2 * chordLength K u x * ENNReal.ofReal (‖x - v‖ ^ n) := by
      calc (2 * (ENNReal.ofReal ‖x - v‖ * chordLength K u x))
            * ENNReal.ofReal (‖x - v‖ ^ (n - 1))
          = 2 * chordLength K u x
              * (ENNReal.ofReal ‖x - v‖ * ENNReal.ofReal (‖x - v‖ ^ (n - 1))) := by ring
        _ = _ := by rw [hprod]
    have step4 : ENNReal.ofReal (‖x - v‖ ^ n) ≤ ENNReal.ofReal (N ^ n * ‖x - u‖ ^ n) := by
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖x - v‖ ^ n ≤ (N * ‖x - u‖) ^ n := pow_le_pow_left₀ (norm_nonneg _) hnorm n
        _ = N ^ n * ‖x - u‖ ^ n := by rw [mul_pow]
    have hsplit1 : ENNReal.ofReal (N ^ n * ‖x - u‖ ^ n)
        = ENNReal.ofReal (N ^ n) * (ENNReal.ofReal (‖x - u‖ ^ (n - 1))
            * ENNReal.ofReal ‖x - u‖) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ‖x - u‖ ^ (n - 1)), hpowu,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ N ^ n)]
    have hsplit2 : c = 2 * ENNReal.ofReal (N ^ n) := by
      rw [hc, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ (2:ℝ)), ENNReal.ofReal_ofNat]
    have step5 : 2 * chordLength K u x * ENNReal.ofReal (N ^ n * ‖x - u‖ ^ n)
        = c * A * ENNReal.ofReal ‖x - u‖ := by
      rw [hsplit1, hA, hsplit2]
      ring
    calc B * ENNReal.ofReal ‖x - u‖ = _ := step1
      _ ≤ _ := step2
      _ = 2 * chordLength K u x * ENNReal.ofReal (‖x - v‖ ^ n) := step3
      _ ≤ 2 * chordLength K u x * ENNReal.ofReal (N ^ n * ‖x - u‖ ^ n) :=
          mul_le_mul' le_rfl step4
      _ = _ := step5
  have hne : ENNReal.ofReal ‖x - u‖ ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hxu0
  have hBA : B ≤ c * A :=
    (ENNReal.mul_le_mul_iff_left hne ENNReal.ofReal_ne_top).1 hmain
  -- invert
  have : (c * A)⁻¹ ≤ B⁻¹ := ENNReal.inv_le_inv.2 hBA
  calc c⁻¹ * hitAndRunDensity K u x = (c * A)⁻¹ := by
        rw [hitAndRunDensity, ← hA, ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
    _ ≤ B⁻¹ := this
    _ = hitAndRunDensity K v x := by rw [hitAndRunDensity, ← hB]

/-- **Integrating the density comparison** against equation (5).  If on `S ∩ K` the
one-step density at `v` dominates `c` times the one at `u`, then `c·P_u(S) ≤ P_v(S)`. -/
theorem mul_hitAndRunProposal_le [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) (u v : EuclideanSpace ℝ (Fin n))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∀ x ∈ S ∩ K, c * hitAndRunDensity K u x ≤ hitAndRunDensity K v x) :
    c * hitAndRunProposal K u S ≤ hitAndRunProposal K v S := by
  rw [hitAndRunProposal_eq_density hKm u hS, hitAndRunProposal_eq_density hKm v hS]
  have hint : c * ∫⁻ x in S ∩ K, hitAndRunDensity K u x
      ≤ ∫⁻ x in S ∩ K, hitAndRunDensity K v x := by
    rw [← lintegral_const_mul' _ _ hc]
    exact setLIntegral_mono' (hS.inter hKm) h
  calc c * (2 / sphereArea n * ∫⁻ x in S ∩ K, hitAndRunDensity K u x)
      = 2 / sphereArea n * (c * ∫⁻ x in S ∩ K, hitAndRunDensity K u x) := by ring
    _ ≤ 2 / sphereArea n * ∫⁻ x in S ∩ K, hitAndRunDensity K v x :=
        mul_le_mul' le_rfl hint

/-! ## `P_u(A₁) ≤ 1/8` -/

/-- **The paper's `P(x ∈ A₁) ≤ 1/8`.**  The *open* ball of radius `F(u)` about `u` carries
at most `1/8` of the one-step law: it is the increasing union of the closed balls of radius
`F(u) − 1/(m+1)`, on each of which
`Arlib.hitAndRun_closedBall_le_of_lt_medianStep` applies. -/
theorem hitAndRun_ball_medianStep_le (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) :
    hitAndRun K u (Metric.ball u (medianStep K u)) ≤ 1 / 8 := by
  set r : ℝ := medianStep K u with hr
  set c : ℕ → ℝ := fun m => r - 1 / (m + 1) with hcdef
  have hmono : Monotone fun m : ℕ => Metric.closedBall u (c m) := by
    intro a b hab
    refine Metric.closedBall_subset_closedBall ?_
    have : (1 : ℝ) / (b + 1) ≤ 1 / (a + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    simp only [hcdef]
    linarith
  have hunion : (⋃ m : ℕ, Metric.closedBall u (c m)) = Metric.ball u r := by
    ext y
    simp only [Set.mem_iUnion, Metric.mem_closedBall, Metric.mem_ball]
    constructor
    · rintro ⟨m, hm⟩
      have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
      simp only [hcdef] at hm
      linarith
    · intro hy
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0:ℝ) < r - dist y u by linarith)
      exact ⟨m, by simp only [hcdef]; linarith⟩
  have hle : ∀ m : ℕ, hitAndRun K u (Metric.closedBall u (c m)) ≤ 1 / 8 := by
    intro m
    refine hitAndRun_closedBall_le_of_lt_medianStep ?_
    have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
    simp only [hcdef]
    linarith
  have htend := tendsto_measure_iUnion_atTop (μ := hitAndRun K u) hmono
  rw [hunion] at htend
  exact le_of_tendsto htend (Filter.Eventually.of_forall hle)

/-! ## The total-variation assembly -/

/-- **From a setwise lower bound off a small set to a total-variation bound.**

If `μ Bad ≤ q` and `c·μ S ≤ ν S` for every measurable `S` disjoint from `Bad`, then
`μ A − ν A ≤ (1 − c) + c·q = 1 − c(1 − q)` for every measurable `A`: this is the last
display of Lovász's proof. -/
theorem tvLe_of_overlap {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Bad : Set Ω} (hBadm : MeasurableSet Bad) {c q : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq0 : 0 ≤ q)
    (hq : μ Bad ≤ ENNReal.ofReal q)
    (hcomp : ∀ S : Set Ω, MeasurableSet S → Disjoint S Bad →
      ENNReal.ofReal c * μ S ≤ ν S) :
    TVLe μ ν (ENNReal.ofReal (1 - c * (1 - q))) := by
  refine tvLe_of_forall_le fun A hA => ?_
  have hAd : MeasurableSet (A \ Bad) := hA.diff hBadm
  have hdisj : Disjoint (A \ Bad) Bad := Set.disjoint_sdiff_left
  have hkey : ENNReal.ofReal c * μ (A \ Bad) ≤ ν A :=
    (hcomp _ hAd hdisj).trans (measure_mono Set.sdiff_subset)
  -- move to reals
  set a : ℝ := (μ A).toReal with ha
  set m : ℝ := (μ (A \ Bad)).toReal with hm
  set b : ℝ := (ν A).toReal with hb
  have ha1 : a ≤ 1 := by
    rw [ha, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hsplit : a ≤ m + q := by
    have h1 : μ A ≤ μ (A \ Bad) + ENNReal.ofReal q := by
      refine (measure_le_inter_add_sdiff μ A Bad).trans ?_
      rw [add_comm]
      exact add_le_add le_rfl ((measure_mono Set.inter_subset_right).trans hq)
    have := ENNReal.toReal_mono (by finiteness) h1
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0] at this
  have hcm : c * m ≤ b := by
    have := ENNReal.toReal_mono (measure_ne_top ν A) hkey
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at this
  have hfinal : a ≤ b + (1 - c * (1 - q)) := by nlinarith [hsplit, hcm, ha1, hc0, hc1, ha0]
  have hμA : μ A = ENNReal.ofReal a := by
    rw [ha, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hνA : ν A = ENNReal.ofReal b := by
    rw [hb, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hμA, hνA, ← ENNReal.ofReal_add hb0 (by nlinarith [hfinal, hb0, ha0])]
  exact ENNReal.ofReal_le_ofReal hfinal

/-! ## The two combined, for the walk -/

/-- **The walk's version of `tvLe_of_overlap`.**  When both walks move with probability one
(`hmoveu`, `hmovev` — the lazy atom of `hitAndRun` is empty), a pointwise density comparison
on `Badᶜ ∩ K` gives a total-variation bound on the one-step laws. -/
theorem tvLe_hitAndRun_of_overlap [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {u v : EuclideanSpace ℝ (Fin n)}
    (hmoveu : hitAndRunProposal K u Set.univ = 1)
    (hmovev : hitAndRunProposal K v Set.univ = 1)
    {Bad : Set (EuclideanSpace ℝ (Fin n))} (hBadm : MeasurableSet Bad) {c q : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq0 : 0 ≤ q)
    (hq : hitAndRun K u Bad ≤ ENNReal.ofReal q)
    (hdens : ∀ x ∈ K, x ∉ Bad →
      ENNReal.ofReal c * hitAndRunDensity K u x ≤ hitAndRunDensity K v x) :
    TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - c * (1 - q))) := by
  have hu : ∀ t : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet t →
      hitAndRun K u t = hitAndRunProposal K u t := by
    intro t ht
    rw [hitAndRun_apply_set hKm u ht, hmoveu, tsub_self, zero_mul, add_zero]
  have hv : ∀ t : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet t →
      hitAndRun K v t = hitAndRunProposal K v t := by
    intro t ht
    rw [hitAndRun_apply_set hKm v ht, hmovev, tsub_self, zero_mul, add_zero]
  refine tvLe_of_overlap hBadm hc0 hc1 hq0 hq ?_
  intro S hS hdisj
  rw [hu S hS, hv S hS]
  refine mul_hitAndRunProposal_le hKm u v hS ENNReal.ofReal_ne_top ?_
  rintro x ⟨hxS, hxK⟩
  exact hdens x hxK (Set.disjoint_left.1 hdisj hxS)

/-! ## Lemma 4.1 -/

/-- **Lemma 4.1 of Lovász–Vempala = Lemma 8 of Lovász (1999).**

If `d_K(u,v) < 1/8` and `|u − v| < (2/√n)·F(u)`, then `d_TV(P_u, P_v) < 1 − 1/500`.

What is proved here is the implication carrying that lemma, with its three geometric inputs
threaded as explicit `∀`-hypotheses because Mathlib v4.32 cannot supply them (see the module
docstring):

* `hcap` — the paper's spherical-cap estimate, `P_u(A₂) ≤ q₂`.  **Unproved.**  The paper's
  value `q₂ = 1/6` is *wrong*; the true value ranges from `1/2` at `n = 2` down to
  `2(1 − Φ(1)) = 0.3173…`.  The statement is parametric in `q₂` for exactly that reason.
* `hA3` — the paper's `P_u(A₃) ≤ 1/3`, written in the chord coordinate of
  `Arlib/Convexity/CrossRatio.lean` as `P_u{x : chordLow K u x < −3} ≤ 1/3`.  **Unproved.**
* `hchord` — the Menelaus chord comparison.  **Unproved.**  Its antecedents are exactly the
  paper's (7), (8) and the complement of `A₃`, together with `d_K(u,v) < 1/8`; `hdK` is
  supplied to it and is used nowhere else.

`P_u(A₁) ≤ 1/8` — the third of the paper's three bad pieces, and the one that is really
about the walk rather than about Euclidean geometry — **is proved**
(`hitAndRun_ball_medianStep_le`), as is the whole density comparison and the assembly.

The constant returned is the *sharp* one, `1 − (1 − q)/(2(1 + 4/n)ⁿ)` with
`q = 1/8 + q₂ + 1/3`, not the paper's rounded `1 − 1/500`; see the module docstring for why
the rounding matters. -/
theorem tvLe_hitAndRun_lemma41 (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {u v : EuclideanSpace ℝ (Fin n)}
    (hmoveu : hitAndRunProposal K u Set.univ = 1)
    (hmovev : hitAndRunProposal K v Set.univ = 1)
    (hdK : crossRatioDist K u v < 1 / 8)
    (hFu : ‖u - v‖ < 2 / Real.sqrt n * medianStep K u)
    {q₂ : ℝ} (hq₂0 : 0 ≤ q₂)
    (hcap : hitAndRun K u
        {x : EuclideanSpace ℝ (Fin n) |
          ‖x - u‖ * ‖u - v‖ < Real.sqrt n * |⟪x - u, u - v⟫|}
      ≤ ENNReal.ofReal q₂)
    (hA3m : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3})
    (hA3 : hitAndRun K u {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
      ≤ ENNReal.ofReal (1 / 3))
    (hchord : ∀ x ∈ K, crossRatioDist K u v < 1 / 8 →
      medianStep K u ≤ ‖x - u‖ →
      Real.sqrt n * |⟪x - u, u - v⟫| ≤ ‖x - u‖ * ‖u - v‖ →
      -3 ≤ chordLow K u x →
      chordLength K v x * ENNReal.ofReal ‖x - u‖
        ≤ 2 * (ENNReal.ofReal ‖x - v‖ * chordLength K u x)) :
    TVLe (hitAndRun K u) (hitAndRun K v)
      (ENNReal.ofReal
        (1 - 1 / (2 * (1 + 4 / (n : ℝ)) ^ n) * (1 - (1 / 8 + q₂ + 1 / 3)))) := by
  haveI : NeZero n := ⟨hn⟩
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  set N : ℝ := 1 + 4 / (n : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have hcpos : (0 : ℝ) < 2 * N ^ n := by positivity
  -- the three bad pieces
  set A₁ : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball u (medianStep K u) with hA₁
  set A₂ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | ‖x - u‖ * ‖u - v‖ < Real.sqrt n * |⟪x - u, u - v⟫|} with hA₂
  set A₃ : Set (EuclideanSpace ℝ (Fin n)) := {x | chordLow K u x < -3} with hA₃def
  set Bad : Set (EuclideanSpace ℝ (Fin n)) := A₁ ∪ A₂ ∪ A₃ with hBad
  have hA₁m : MeasurableSet A₁ := measurableSet_ball
  have hA₂m : MeasurableSet A₂ := by
    have h1 : Continuous fun x : EuclideanSpace ℝ (Fin n) => ‖x - u‖ * ‖u - v‖ := by fun_prop
    have h2 : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
        Real.sqrt n * |⟪x - u, u - v⟫| := by
      exact continuous_const.mul ((continuous_id.sub continuous_const).inner
        continuous_const).abs
    exact measurableSet_lt h1.measurable h2.measurable
  have hA₃m : MeasurableSet A₃ := hA3m
  have hBadm : MeasurableSet Bad := (hA₁m.union hA₂m).union hA₃m
  -- the mass of `Bad`
  have hq : hitAndRun K u Bad ≤ ENNReal.ofReal (1 / 8 + q₂ + 1 / 3) := by
    refine (measure_union_le _ _).trans ?_
    refine ((add_le_add ((measure_union_le _ _).trans
      (add_le_add (hitAndRun_ball_medianStep_le K u) hcap)) hA3)).trans ?_
    rw [ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 1/8 + q₂) (by norm_num : (0:ℝ) ≤ 1/3),
      ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1/8) hq₂0]
    have : (1 : ℝ≥0∞) / 8 = ENNReal.ofReal (1 / 8) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    rw [this]
  -- the density comparison off `Bad`
  have hdens : ∀ x ∈ K, x ∉ Bad →
      ENNReal.ofReal (1 / (2 * N ^ n)) * hitAndRunDensity K u x
        ≤ hitAndRunDensity K v x := by
    intro x hxK hxBad
    have h1 : x ∉ A₁ := fun h => hxBad (Or.inl (Or.inl h))
    have h2 : x ∉ A₂ := fun h => hxBad (Or.inl (Or.inr h))
    have h3 : x ∉ A₃ := fun h => hxBad (Or.inr h)
    have hFle : medianStep K u ≤ ‖x - u‖ := by
      by_contra hcon
      refine h1 ?_
      rw [hA₁, Metric.mem_ball, dist_eq_norm]
      exact lt_of_not_ge hcon
    have h8 : Real.sqrt n * |⟪x - u, u - v⟫| ≤ ‖x - u‖ * ‖u - v‖ := by
      rw [hA₂, Set.mem_setOf_eq, not_lt] at h2
      exact h2
    have h3' : (-3 : ℝ) ≤ chordLow K u x := by
      rw [hA₃def, Set.mem_setOf_eq, not_lt] at h3
      exact h3
    -- the paper's (7)
    have h7 : Real.sqrt n * ‖u - v‖ ≤ 2 * ‖x - u‖ := by
      have : ‖u - v‖ < 2 / Real.sqrt n * ‖x - u‖ :=
        lt_of_lt_of_le hFu (by
          apply mul_le_mul_of_nonneg_left hFle
          positivity)
      have hmul := (mul_lt_mul_of_pos_left this hspos)
      rw [show Real.sqrt n * (2 / Real.sqrt n * ‖x - u‖) = 2 * ‖x - u‖ by
        field_simp] at hmul
      exact hmul.le
    have hFpos : 0 < medianStep K u := by
      rcases le_or_gt (medianStep K u) 0 with hle | hgt
      · exfalso
        have h2s : (0 : ℝ) < 2 / Real.sqrt n := by positivity
        have hnp : 2 / Real.sqrt n * medianStep K u ≤ 0 := by nlinarith [h2s, hle]
        have := norm_nonneg (u - v)
        linarith [hFu]
      · exact hgt
    have hxu : x ≠ u := by
      intro h
      rw [h] at hFle
      simp only [sub_self, norm_zero] at hFle
      linarith
    have hnorm : ‖x - v‖ ≤ N * ‖x - u‖ :=
      norm_sub_le_of_almost_orthogonal hn u v x h7 h8
    have hch := hchord x hxK hdK hFle h8 h3'
    have := hitAndRunDensity_ge_of_chordLength_le (K := K) hn hxu hNpos hnorm hch
    rwa [show ENNReal.ofReal (1 / (2 * N ^ n)) = (ENNReal.ofReal (2 * N ^ n))⁻¹ by
      rw [one_div, ENNReal.ofReal_inv_of_pos hcpos]]
  refine tvLe_hitAndRun_of_overlap hKm hmoveu hmovev hBadm ?_ ?_ ?_ hq hdens
  · positivity
  · have hone : (1 : ℝ) ≤ N ^ n := by
      refine one_le_pow₀ ?_
      rw [hN]
      have : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
      linarith
    rw [div_le_one hcpos]
    linarith
  · linarith

/-- **Lemma 4.1 with the dimension-free cap bound `q₂ = 1/2`.**

`q₂ = 1/2` is the value of the paper's cap probability at `n = 2`, and it is an upper bound
for every `n ≥ 2` (the probability decreases to `0.3173…`).  With it the proof yields
`1 − 1/2880` at the paper's rounding `2(1 + 4/n)ⁿ ≤ 120`.  This is *weaker* than the
printed `1 − 1/500`, which needs the sharp asymptotic cap constant; see the module
docstring. -/
theorem tvLe_hitAndRun_lemma41_of_half (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKm : MeasurableSet K) {u v : EuclideanSpace ℝ (Fin n)}
    (hmoveu : hitAndRunProposal K u Set.univ = 1)
    (hmovev : hitAndRunProposal K v Set.univ = 1)
    (hdK : crossRatioDist K u v < 1 / 8)
    (hFu : ‖u - v‖ < 2 / Real.sqrt n * medianStep K u)
    (hcap : hitAndRun K u
        {x : EuclideanSpace ℝ (Fin n) |
          ‖x - u‖ * ‖u - v‖ < Real.sqrt n * |⟪x - u, u - v⟫|}
      ≤ ENNReal.ofReal (1 / 2))
    (hA3m : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3})
    (hA3 : hitAndRun K u {x : EuclideanSpace ℝ (Fin n) | chordLow K u x < -3}
      ≤ ENNReal.ofReal (1 / 3))
    (hchord : ∀ x ∈ K, crossRatioDist K u v < 1 / 8 →
      medianStep K u ≤ ‖x - u‖ →
      Real.sqrt n * |⟪x - u, u - v⟫| ≤ ‖x - u‖ * ‖u - v‖ →
      -3 ≤ chordLow K u x →
      chordLength K v x * ENNReal.ofReal ‖x - u‖
        ≤ 2 * (ENNReal.ofReal ‖x - v‖ * chordLength K u x)) :
    TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 2880)) := by
  refine (tvLe_hitAndRun_lemma41 hn hKm hmoveu hmovev hdK hFu (by norm_num)
    hcap hA3m hA3 hchord).mono ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have h := one_div_le_inv_two_mul_pow n
  nlinarith [h]

/-! ### Axiom profile -/

section AxiomCheck

#print axioms norm_sub_le_of_almost_orthogonal
#print axioms pow_one_add_four_div_le_exp
#print axioms two_mul_exp_four_lt
#print axioms one_div_le_inv_two_mul_pow
#print axioms hitAndRunDensity_ge_of_chordLength_le
#print axioms mul_hitAndRunProposal_le
#print axioms hitAndRun_ball_medianStep_le
#print axioms tvLe_of_overlap
#print axioms tvLe_hitAndRun_of_overlap
#print axioms tvLe_hitAndRun_lemma41
#print axioms tvLe_hitAndRun_lemma41_of_half

end AxiomCheck

end Arlib.MarkovChains
