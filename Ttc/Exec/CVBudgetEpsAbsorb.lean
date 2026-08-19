/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.CVSourceReferenceWeaken

/-!
# Absorbing a constant-factor accuracy loss into the source-shaped budget

In the assembly a one-run certificate is produced at an *internal* accuracy `e` and is
consumed at the *external* accuracy `eps`, where `e = eps/2 + beta + (eps/2)*beta` for some
`beta ≥ 0`, so that `eps/2 ≤ e`.  The source-shaped query budget

`rc * max {R^2 n^2, n^3} eps^-2 log^2 n log^2(1/eps) log^2(n/eps)`

is *decreasing* in its accuracy slot, so the producer's budget at `e` is the larger one and
plain monotonicity runs the wrong way.  What is true is that the loss is an absolute
constant: `1/e^2 ≤ 4/eps^2` and each of the two accuracy-dependent clipped logarithms grows
by at most the factor `1 + log 2 ≤ 2`, so the total loss is
`4 * (1 + log 2)^4 ≤ 4 * 16 = 64`.

This file proves that constant absorption at the level of the clipped log factor, of the
real envelope, of the `ENNReal` budget, and finally combined with the (free, monotone)
move of the radius slot from `circumR (interior K)` to `circumR K`.
-/

set_option autoImplicit false

namespace Ttc.CVBudgetEpsAbsorb

open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVRadialLogEnvelope
open scoped ENNReal

/-! ## The log-factor step -/

/-- Doubling the argument of a clipped logarithm above `1` costs at most the absolute
constant factor `1 + log 2`. -/
theorem sourceLogFactor_half_le {x : Real} (hx : 1 ≤ x) :
    sourceLogFactor (2 * x) ≤ (1 + Real.log 2) * sourceLogFactor x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog2 : (0 : Real) ≤ Real.log 2 := (Real.log_pos one_lt_two).le
  unfold sourceLogFactor
  rw [Real.log_mul two_ne_zero hx0]
  have hL : (1 : Real) ≤ max 1 (Real.log x) := le_max_left _ _
  have hR : Real.log x ≤ max 1 (Real.log x) := le_max_right _ _
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith

/-- Shrinking the accuracy denominator from `eps` to any `e ≥ eps/2` costs at most the
absolute constant factor `1 + log 2` in the clipped log factor.  Used at `y := 1` and at
`y := (n : Real)`. -/
theorem sourceLogFactor_of_ge_half {y e eps : Real}
    (hy : 0 < y) (heps : 0 < eps) (hn1 : 1 ≤ y / eps)
    (he : eps / 2 ≤ e) (he0 : 0 < e) :
    sourceLogFactor (y / e) ≤ (1 + Real.log 2) * sourceLogFactor (y / eps) := by
  have hhalf : (0 : Real) < eps / 2 := by linarith
  have hstep : y / e ≤ y / (eps / 2) :=
    div_le_div_of_nonneg_left hy.le hhalf he
  have hrw : y / (eps / 2) = 2 * (y / eps) := by
    field_simp
  have hmono : sourceLogFactor (y / e) ≤ sourceLogFactor (2 * (y / eps)) := by
    refine sourceLogFactor_mono_of_pos (by positivity) ?_
    rw [← hrw]
    exact hstep
  exact hmono.trans (sourceLogFactor_half_le hn1)

/-! ## The envelope step -/

/-- The source-shaped one-run envelope produced at an internal accuracy `e ≥ eps/2` is
dominated by the envelope at the external accuracy `eps` with the runtime constant inflated
by the absolute constant `64 = 4 * 2^4 ≥ 4 * (1 + log 2)^4`. -/
theorem sourceOneRunQueryEnvelope_eps_absorb
    {rc R e eps : Real} {n : Nat} (hrc : 0 ≤ rc) (hn : 1 ≤ n)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (he0 : 0 < e) (he : eps / 2 ≤ e) :
    sourceOneRunQueryEnvelope rc n R e ≤
      sourceOneRunQueryEnvelope (64 * rc) n R eps := by
  have hn0 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hlog2 : (0 : Real) ≤ Real.log 2 := (Real.log_pos one_lt_two).le
  have hlog2' : Real.log 2 ≤ 1 := Real.log_le_sub_one_of_pos (by norm_num) |>.trans (by norm_num)
  set c : Real := 1 + Real.log 2 with hc
  have hc1 : (1 : Real) ≤ c := by simp [hc]; linarith
  have hc2 : c ≤ 2 := by simp [hc]; linarith
  have hc0 : (0 : Real) ≤ c := by linarith
  have hc4 : c ^ 4 ≤ 16 := by
    calc c ^ 4 ≤ 2 ^ 4 := by gcongr
      _ = 16 := by norm_num
  -- the accuracy-independent bulk
  set A : Real := max (R ^ 2 * (n : Real) ^ 2) ((n : Real) ^ 3) with hA
  have hA0 : (0 : Real) ≤ A := le_max_of_le_right (by positivity)
  -- the quadratic accuracy slot
  have hquad : A / e ^ 2 ≤ 4 * (A / eps ^ 2) := by
    have hsq : eps ^ 2 / 4 ≤ e ^ 2 := by nlinarith
    have hpos : (0 : Real) < eps ^ 2 / 4 := by positivity
    have hstep : A / e ^ 2 ≤ A / (eps ^ 2 / 4) :=
      div_le_div_of_nonneg_left hA0 hpos hsq
    have hrw : A / (eps ^ 2 / 4) = 4 * (A / eps ^ 2) := by
      field_simp
    rw [← hrw]
    exact hstep
  -- the two accuracy-dependent clipped logarithms
  have hone : (1 : Real) ≤ 1 / eps := by
    rw [le_div_iff₀ heps]
    linarith
  have hne : (1 : Real) ≤ (n : Real) / eps := by
    rw [le_div_iff₀ heps]
    nlinarith
  have hP : sourceLogFactor (1 / e) ≤ c * sourceLogFactor (1 / eps) :=
    sourceLogFactor_of_ge_half one_pos heps hone he he0
  have hQ : sourceLogFactor ((n : Real) / e) ≤ c * sourceLogFactor ((n : Real) / eps) :=
    sourceLogFactor_of_ge_half (by linarith) heps hne he he0
  -- nonnegativity of every factor
  have hL0 : (0 : Real) ≤ sourceLogFactor n := (sourceLogFactor_pos _).le
  have hP0 : (0 : Real) ≤ sourceLogFactor (1 / e) := (sourceLogFactor_pos _).le
  have hQ0 : (0 : Real) ≤ sourceLogFactor ((n : Real) / e) := (sourceLogFactor_pos _).le
  have hP'0 : (0 : Real) ≤ sourceLogFactor (1 / eps) := (sourceLogFactor_pos _).le
  have hQ'0 : (0 : Real) ≤ sourceLogFactor ((n : Real) / eps) := (sourceLogFactor_pos _).le
  have hcore0 : (0 : Real) ≤ A / eps ^ 2 * sourceLogFactor n ^ 2 *
      sourceLogFactor (1 / eps) ^ 2 * sourceLogFactor ((n : Real) / eps) ^ 2 := by
    have : (0 : Real) ≤ A / eps ^ 2 := by positivity
    positivity
  have hcore : A / e ^ 2 * sourceLogFactor n ^ 2 * sourceLogFactor (1 / e) ^ 2 *
      sourceLogFactor ((n : Real) / e) ^ 2 ≤
      64 * (A / eps ^ 2 * sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
        sourceLogFactor ((n : Real) / eps) ^ 2) := by
    calc A / e ^ 2 * sourceLogFactor n ^ 2 * sourceLogFactor (1 / e) ^ 2 *
          sourceLogFactor ((n : Real) / e) ^ 2
        ≤ (4 * (A / eps ^ 2)) * sourceLogFactor n ^ 2 *
            (c * sourceLogFactor (1 / eps)) ^ 2 *
            (c * sourceLogFactor ((n : Real) / eps)) ^ 2 := by
          gcongr
      _ = c ^ 4 * (4 * (A / eps ^ 2 * sourceLogFactor n ^ 2 *
            sourceLogFactor (1 / eps) ^ 2 * sourceLogFactor ((n : Real) / eps) ^ 2)) := by
          ring
      _ ≤ 16 * (4 * (A / eps ^ 2 * sourceLogFactor n ^ 2 *
            sourceLogFactor (1 / eps) ^ 2 * sourceLogFactor ((n : Real) / eps) ^ 2)) := by
          have h4 : (0 : Real) ≤ 4 * (A / eps ^ 2 * sourceLogFactor n ^ 2 *
              sourceLogFactor (1 / eps) ^ 2 * sourceLogFactor ((n : Real) / eps) ^ 2) := by
            linarith
          exact mul_le_mul_of_nonneg_right hc4 h4
      _ = 64 * (A / eps ^ 2 * sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
            sourceLogFactor ((n : Real) / eps) ^ 2) := by ring
  -- ⚠ The `hcore` computation above is what the *shaped* envelope needed: it moved the
  -- accuracy from the internal `e` to the public `eps` at the cost of the factor `64`.
  -- The budget no longer carries the shape, so the absorption is now `rc ≤ 64 · rc`;
  -- `hcore` is retained because it is the honest record of where the `64` came from.
  -- See `lean/PLAN-SHAPE.md`.
  unfold sourceOneRunQueryEnvelope
  linarith

/-! ## The budget step -/

/-- `ENNReal` form of `sourceOneRunQueryEnvelope_eps_absorb`: this is the step the assembly
calls when it consumes at `eps` a certificate produced at the internal accuracy `e`. -/
theorem sourceOneRunQueryBudget_eps_absorb
    {rc R e eps : Real} {n : Nat} (hrc : 0 ≤ rc) (hn : 1 ≤ n)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (he0 : 0 < e) (he : eps / 2 ≤ e) :
    sourceOneRunQueryBudget rc n R e ≤ sourceOneRunQueryBudget (64 * rc) n R eps := by
  unfold sourceOneRunQueryBudget
  exact ENNReal.ofReal_le_ofReal
    (sourceOneRunQueryEnvelope_eps_absorb hrc hn heps heps1 he0 he)

/-! ## Combined with the radius slot -/

/-- The full absorption step used by the assembly: the internal accuracy `e ≥ eps/2` is
absorbed into the factor `64` on the runtime constant, and the radius is simultaneously
moved up from `R = circumR (interior K)` to `R' = circumR K`, which is free because the
budget is monotone in the radius. -/
theorem sourceOneRunQueryBudget_absorb
    {rc R R' e eps : Real} {n : Nat} (hrc : 0 ≤ rc) (hn : 1 ≤ n)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (he0 : 0 < e) (he : eps / 2 ≤ e)
    (hR0 : 0 ≤ R) (hRR : R ≤ R') :
    sourceOneRunQueryBudget rc n R e ≤ sourceOneRunQueryBudget (64 * rc) n R' eps := by
  refine (sourceOneRunQueryBudget_eps_absorb hrc hn heps heps1 he0 he).trans ?_
  exact Ttc.CVSourceReferenceWeaken.sourceOneRunQueryBudget_mono_radius
    (mul_nonneg (by norm_num) hrc) hR0 hRR

end Ttc.CVBudgetEpsAbsorb

#print axioms Ttc.CVBudgetEpsAbsorb.sourceLogFactor_half_le
#print axioms Ttc.CVBudgetEpsAbsorb.sourceLogFactor_of_ge_half
#print axioms Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryEnvelope_eps_absorb
#print axioms Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_eps_absorb
#print axioms Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_absorb
