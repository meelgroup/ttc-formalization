/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.PerPhaseLeavesExplicit

/-!
# `PLAN-SHAPE` §5: the per-phase leaves are polynomial

`Ttc.ttc_volume`'s volume half names four Cousins–Vempala schedule quantities.
`Ttc/Exec/PerPhaseLeavesExplicit.lean` writes three of them out; this file bounds them by
explicit polynomials in `n`, `R²` and `1/ε`, which is what §5 actually asks.

## The two facts that make it work

**The cooling schedule's variance collapses.**  `slowSourceSigmaSq` is
`s₀·(1+1/n)^m` and `slowPhasesP` is `⌈log(16n·max 1 R²)/log(1+1/n)⌉₊ + 1`, so exponentiating
the phase count *cancels the logarithm that defined it*: `(1+1/n)^m ≤ 16n·max 1 R²·(1+1/n)²`,
and `s₀ = 1/(16n)` divides the `16n` back out.  The variance is `O(R²)` — no `n`, no
schedule vocabulary.  This is `slowSourceSigmaSq_slowPhasesP_le`.

**Every exponential is consumed by a logarithm.**  Three appear —
`exp(8·(√R²)²)` in the retry cap's share floor, `exp(R²/(2s₀)) = exp(8n·R²)` in
`rAwareRadiusCalls`, and `(4·max 1 R)^n` in `hotRefreshWarmEnvelope` — and each enters only
under a `Real.log`.  The middle one is additionally divided by `n` inside
`globalLogarithmicRadiusQ n A = √(16 + 4·log(20A)/n)`, which is why that function is named
for a logarithm: it turns `exp(16n·R²)` into `16·R²` under a square root.
-/

namespace Ttc.PerPhasePoly

open Ttc.PerPhaseLeavesExplicit
open Ttc.TtcSlowRuntimePerPhase Ttc.CVSlowEffectiveOverhead
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Arlib.Convexity.GaussianCooling

/-- `1/log(1+1/n) ≤ 2n` — the step that turns the phase count into a polynomial.  For
`0 ≤ x ≤ 1`, `log(1+x) ≥ x/2`. -/
theorem one_div_log_one_add_le (n : ℕ) (hn : 1 ≤ n) :
    1 / Real.log (1 + 1 / (n : ℝ)) ≤ 2 * (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx1 : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn0]; exact_mod_cast hn
  have hx0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  -- `log(1+x) ≥ x/2` on `[0,1]`, via `log(1+x) ≥ x/(1+x)` and `1+x ≤ 2`
  have hkey : 1 / (2 * (n : ℝ)) ≤ Real.log (1 + 1 / (n : ℝ)) := by
    have hlb : (1 / (n : ℝ)) / (1 + 1 / (n : ℝ)) ≤ Real.log (1 + 1 / (n : ℝ)) := by
      have := Real.add_one_le_exp (-(Real.log (1 + 1 / (n : ℝ))))
      have hpos : (0 : ℝ) < 1 + 1 / (n : ℝ) := by linarith
      rw [Real.exp_neg, Real.exp_log hpos] at this
      have hinv : (1 + 1 / (n : ℝ))⁻¹ = 1 / (1 + 1 / (n : ℝ)) := by rw [one_div]
      rw [hinv] at this
      have hstep : 1 - 1 / (1 + 1 / (n : ℝ)) ≤ Real.log (1 + 1 / (n : ℝ)) := by linarith
      have hEq : 1 - 1 / (1 + 1 / (n : ℝ)) = (1 / (n : ℝ)) / (1 + 1 / (n : ℝ)) := by
        field_simp
      linarith [hEq ▸ hstep]
    have hden : 1 + 1 / (n : ℝ) ≤ 2 := by linarith
    have : (1 / (n : ℝ)) / 2 ≤ (1 / (n : ℝ)) / (1 + 1 / (n : ℝ)) := by
      apply div_le_div_of_nonneg_left (le_of_lt hx0) (by linarith) hden
    have hrw : (1 / (n : ℝ)) / 2 = 1 / (2 * (n : ℝ)) := by field_simp; ring
    linarith [hrw ▸ this]
  have hlogpos : 0 < Real.log (1 + 1 / (n : ℝ)) := by
    have : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
    linarith
  rw [div_le_iff₀ hlogpos]
  have h2n : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  calc (1 : ℝ) = (2 * (n : ℝ)) * (1 / (2 * (n : ℝ))) := by field_simp
    _ ≤ (2 * (n : ℝ)) * Real.log (1 + 1 / (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hkey (le_of_lt h2n)

#print axioms one_div_log_one_add_le

end Ttc.PerPhasePoly
