/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Probability.Moments.SubGaussian
import Ttc.Internal.Arith

/-!
# `claim:cl`: the concentration core of the randomized rounding

`claim:cl` of the paper bounds, for the randomized rounding `rnd` of a uniform point,
the probability of crossing an inflated/deflated facet. Its whole probabilistic
content is a single tail estimate: writing `Y = p − rnd(p)` for the rounding
displacement, the paper bounds

  `Pr[A_ij · Y ≥ κ‖A_ij‖]`

by an Azuma/martingale argument. Since the coordinates of `Y` are rounded
independently, each `Y_k` lies in `[−1,1]` and has mean zero, this is exactly
**Hoeffding's inequality for independent bounded variables**, which Mathlib has.

This file proves that tail bound (`Ttc.rounding_tail_bound`), specialises it at the
paper's `κ` (`Ttc.rounding_tail_bound_kappa`), and does the union bound over all
`r` facets (`Ttc.rounding_union_bound`). Together these are the quantitative heart
of `claim:cl`.

## What is proved and what is not

Proved: the concentration estimate, at the paper's parameters, for **any**
independent mean-zero displacement supported in `[−1,1]ⁿ` — which is what any
coordinatewise randomized rounding produces.

Not proved: the *reduction* of `claim:cl`(a)/(b)/(c) to this estimate, i.e. the
integral manipulations `Pr[rnd p = x] = (1/vol Q')∫_{Q'} Pr(x + Y = p)\,dp` and
`∫_{C(x)} Pr(x+Y=p)\,dp = 1`. Those require a measure-theoretic model of `rnd`
that is orthogonal to the paper's mathematical content; they remain the residual
assumption in `Ttc.TtcAnalysis`.

## Bug-oracle finding: a missing square in the Azuma exponent

`sections/proof-appendix.tex:69` (inside the commented-out proof of `claim:cl`)
displays

  `Pr(A_ij Y ≥ κ) ≤ 2 exp(−κ²‖A_ij‖ / (2 ∑_{k'} |A_ijk'|²))`.

Since `∑_{k'} |A_ijk'|² = ‖A_ij‖²`, that exponent is `−κ²/(2‖A_ij‖)`, which is not
scale-invariant and does not give the claimed `η/(2r)`. The correct exponent —
and the one Hoeffding actually yields for the event `A_ij·Y ≥ κ‖A_ij‖` — is

  `−(κ‖A_ij‖)² / (2 ∑_{k'} |A_ijk'|²) = −κ²/2`,

i.e. the numerator needs `‖A_ij‖²`, not `‖A_ij‖`. With the square restored the
chain works: `exp(−κ²/2) ≤ η/(4r)` at the paper's `κ`, so the union bound over the
`r` facets gives `η/4`, comfortably inside the `η/2` the proof needs. The claim is
therefore **true as used**; only the displayed exponent is wrong.

Note also that the event is one-sided, so the leading factor `2` in the paper's
display is unnecessary — which is where the slack between `η/4` and `η/2` comes
from.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Euclidean norm of a coefficient vector, as the paper's `‖A_ij‖`. -/
noncomputable def coeffNorm {n : ℕ} (A : Fin n → ℝ) : ℝ := Real.sqrt (∑ k, A k ^ 2)

theorem coeffNorm_sq {n : ℕ} (A : Fin n → ℝ) : coeffNorm A ^ 2 = ∑ k, A k ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem coeffNorm_nonneg {n : ℕ} (A : Fin n → ℝ) : 0 ≤ coeffNorm A := Real.sqrt_nonneg _

/-- Each scaled coordinate `A k * Y k` is sub-Gaussian with proxy `A k ^ 2`,
by Hoeffding's lemma for bounded mean-zero variables. -/
theorem hasSubgaussianMGF_coeff_mul {n : ℕ} (Y : Fin n → Ω → ℝ) (A : Fin n → ℝ)
    (k : Fin n) (hmeas : AEMeasurable (Y k) μ)
    (hbdd : ∀ᵐ ω ∂μ, Y k ω ∈ Set.Icc (-1 : ℝ) 1) (hmean : μ[Y k] = 0) :
    HasSubgaussianMGF (fun ω => A k * Y k ω) (‖A k‖₊ ^ 2) μ := by
  have hbdd' : ∀ᵐ ω ∂μ, (A k * Y k ω) ∈ Set.Icc (-|A k|) |A k| := by
    filter_upwards [hbdd] with ω hω
    rw [Set.mem_Icc, ← abs_le, abs_mul]
    have h1 : |Y k ω| ≤ 1 := abs_le.2 ⟨hω.1, hω.2⟩
    nlinarith [abs_nonneg (A k), abs_nonneg (Y k ω)]
  have hmean' : μ[fun ω => A k * Y k ω] = 0 := by
    rw [integral_const_mul, hmean, mul_zero]
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := fun ω => A k * Y k ω) (a := -|A k|) (b := |A k|)
    (hmeas.const_mul _) hbdd' hmean'
  have hcoef : (‖|A k| - -|A k|‖₊ / 2) ^ 2 = ‖A k‖₊ ^ 2 := by
    rw [show |A k| - -|A k| = 2 * |A k| by ring]
    rw [show (2 : ℝ) * |A k| = |(2 : ℝ) * A k| by rw [abs_mul]; norm_num]
    simp [nnnorm_mul]
  rwa [hcoef] at h

/-- **The concentration core of `claim:cl`.**

If the rounding displacement `Y` has independent coordinates, each supported in
`[−1,1]` with mean zero, then for any coefficient vector `A` and any `κ ≥ 0`,

  `Pr[ κ‖A‖ ≤ A · Y ] ≤ exp(−κ²/2)`.

This is Hoeffding's inequality; it is the corrected form of the paper's Azuma
step (see the module docstring for the missing square). -/
theorem rounding_tail_bound {n : ℕ} (Y : Fin n → Ω → ℝ) (A : Fin n → ℝ)
    (hmeas : ∀ k, AEMeasurable (Y k) μ)
    (hindep : iIndepFun (fun k ω => A k * Y k ω) μ)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, Y k ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ k, μ[Y k] = 0)
    {κ : ℝ} (hκ : 0 ≤ κ) (hA : 0 < ∑ k, A k ^ 2) :
    μ.real {ω | κ * coeffNorm A ≤ ∑ k, A k * Y k ω} ≤ Real.exp (-κ ^ 2 / 2) := by
  have hsubG : ∀ k ∈ Finset.univ,
      HasSubgaussianMGF (fun ω => A k * Y k ω) (‖A k‖₊ ^ 2) μ :=
    fun k _ => hasSubgaussianMGF_coeff_mul Y A k (hmeas k) (hbdd k) (hmean k)
  have hNpos : 0 < coeffNorm A := Real.sqrt_pos.2 hA
  have hε : 0 ≤ κ * coeffNorm A := mul_nonneg hκ (le_of_lt hNpos)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep (s := Finset.univ) hsubG hε
  -- identify `∑ k, ‖A k‖₊ ^ 2` with `‖A‖²` and simplify the exponent
  have hsum : ((∑ k, ‖A k‖₊ ^ 2 : NNReal) : ℝ) = ∑ k, A k ^ 2 := by
    push_cast
    exact Finset.sum_congr rfl fun k _ => by rw [Real.norm_eq_abs, sq_abs]
  refine le_trans h (le_of_eq ?_)
  congr 1
  rw [hsum, ← coeffNorm_sq A]
  have hNne : coeffNorm A ≠ 0 := ne_of_gt hNpos
  field_simp

/-- **`claim:cl` at the paper's `κ`.** With
`κ = √(2 log(4/η)) + √(2 log r)`, the tail bound is at most `η/(4r)`. -/
theorem rounding_tail_bound_kappa {n : ℕ} (Y : Fin n → Ω → ℝ) (A : Fin n → ℝ)
    (hmeas : ∀ k, AEMeasurable (Y k) μ)
    (hindep : iIndepFun (fun k ω => A k * Y k ω) μ)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, Y k ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ k, μ[Y k] = 0)
    {η r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r) (hA : 0 < ∑ k, A k ^ 2) :
    μ.real {ω | (Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r)) * coeffNorm A
        ≤ ∑ k, A k * Y k ω} ≤ η / (4 * r) := by
  set κ : ℝ := Real.sqrt (2 * Real.log (4 / η)) + Real.sqrt (2 * Real.log r) with hκdef
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hlogη : 0 ≤ Real.log (4 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη]; linarith)
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  -- `κ² ≥ 2 log(4/η) + 2 log r`
  have hκsq : 2 * Real.log (4 / η) + 2 * Real.log r ≤ κ ^ 2 := by
    rw [hκdef, add_sq, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    have : 0 ≤ 2 * Real.sqrt (2 * Real.log (4 / η)) * Real.sqrt (2 * Real.log r) := by
      positivity
    linarith
  -- `exp(-κ²/2) ≤ η/(4r)`
  have hexp : Real.exp (-κ ^ 2 / 2) ≤ η / (4 * r) := by
    have hsplit : Real.log (4 * r / η) = Real.log (4 / η) + Real.log r := by
      rw [show (4 : ℝ) * r / η = (4 / η) * r by ring,
        Real.log_mul (by positivity) (by linarith)]
    have hle : -κ ^ 2 / 2 ≤ -Real.log (4 * r / η) := by
      rw [hsplit]; linarith
    calc Real.exp (-κ ^ 2 / 2) ≤ Real.exp (-Real.log (4 * r / η)) := Real.exp_le_exp.2 hle
      _ = (4 * r / η)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
      _ = η / (4 * r) := by rw [inv_div]
  exact le_trans (rounding_tail_bound Y A hmeas hindep hbdd hmean hκ0 hA) hexp

/-- **The union bound of `claim:cl`.** Summing the per-facet tail bound over the `r`
facets of the whole family gives `η/4` — half of the `η/2` the paper's proof
consumes, the slack coming from the fact that the crossing event is one-sided. -/
theorem rounding_union_bound {ι : Type*} (T : Finset ι) (pr : ι → ℝ)
    {η r : ℝ} (hr : 0 < r) (hcard : (T.card : ℝ) ≤ r)
    (hbound : ∀ i ∈ T, pr i ≤ η / (4 * r)) (hη : 0 ≤ η) :
    ∑ i ∈ T, pr i ≤ η / 4 := by
  calc ∑ i ∈ T, pr i ≤ ∑ _i ∈ T, η / (4 * r) := Finset.sum_le_sum hbound
    _ = (T.card : ℝ) * (η / (4 * r)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ r * (η / (4 * r)) := by
        apply mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = η / 4 := by field_simp

end Ttc
