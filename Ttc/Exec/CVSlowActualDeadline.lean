import Ttc.Exec.CVSpeedyDeadlineMono
import Ttc.Exec.CVSlowWarmBudgetBound

/-!
# The deadline the slow canonical schedule actually selects

The frontier theorem's `hsteps` binder is about

```
slowCanonicalSteps initialWarm n q s0 K retries eta zeta i _
  = adjustableSpeedyDeadline n (radiusQDelta n q sigma_i) sigma_i
      ((2 * slowWarmBudget initialWarm n q s0 K retries i) / eta i) (zeta i)
```

whose warmness argument is the **recursively compounding actual-path** budget
`slowWarmBudget`, while every deadline cap in the repository
(`slowScoreAwareSteps_canonical_active_le`, `slowScoreAwareSteps_uniform_active_le`) is
proved for the **fixed reference** warm `slowReferenceWarm`.  That mismatch is why `hsteps`
had no provider.

This file bridges the two.  It is stated with the warmness bound as a *hypothesis on the
logarithm*, `Real.log (slowWarmBudget … i).toReal ≤ Wlog`, because that is the shape the
compounding recursion actually admits: `recursiveWarmBudget_le_product` gives a product,
and its logarithm is a sum — additive in the phase index, hence polynomial.  Supplying
`Wlog` is the job of `Ttc/Exec/CVSlowWarmBudgetBound.lean`.

## Main results

* `slowActualDeadlineExpression` — the real deadline envelope at a warmness-log bound.
* `slowCanonicalSteps_le_ceil_of_log_le` — the `hsteps` shape, at that envelope.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Ttc.CVSlowActualDeadline

open MeasureTheory Metric Set
open Ttc.CVSpeedyDeadlineMono
open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVSlowRadiusQCanonicalOperational
open Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowWarmBudgetBound
open scoped ENNReal

variable {n : Nat}

local notation "State" => fun m => EuclideanSpace Real (Fin m)

/-- The real deadline envelope, at a bound `Wlog` on the logarithm of the actual warm
budget and a bound `Elog` on `Real.log (1 / eta.toReal)`.

The `Real.log 2` summand is the explicit `2 *` in `slowCanonicalSteps`'s warmness argument;
`Wlog` is the compounding budget's contribution; `Elog` bounds the share dividing that
warmness (`etaShare`); and `Zlog` bounds the *separate* share the deadline itself consumes
(`zetaShare`).  The two shares are genuinely different arguments of `slowCanonicalSteps` —
`etaShare` divides the warm budget inside `M`, while `zetaShare` is the deadline's own `eta`
slot — and conflating them is a type error, which is how this was found. -/
noncomputable def slowActualDeadlineExpression
    (n : Nat) (delta sigmaSq Wlog Elog Zlog : Real) : Real :=
  4 * 640 ^ 2 * sigmaSq * (n : Real) *
      ((Real.log 2 + Wlog + Elog) + 2 * Zlog) / (delta * Real.log 2) ^ 2 + 1

/-- The warmness argument's logarithm splits into the explicit factor `2`, the budget, and
the share.  Stated as an inequality rather than an identity so the degenerate `ENNReal`
cases (`eta = 0`, `eta = ⊤`, a non-finite budget) do not have to be excluded by hypothesis
— they are excluded by the finiteness and positivity arguments the caller already has. -/
theorem log_two_mul_div_le
    {W eta : ENNReal} {Wlog Elog : Real}
    (hW : W ≠ ⊤) (hW0 : 0 < W.toReal)
    (heta : eta ≠ 0) (heta' : eta ≠ ⊤)
    (hWlog : Real.log W.toReal ≤ Wlog)
    (hElog : Real.log (1 / eta.toReal) ≤ Elog) :
    Real.log ((2 * W / eta).toReal) ≤ Real.log 2 + Wlog + Elog := by
  have heta0 : 0 < eta.toReal := ENNReal.toReal_pos heta heta'
  have htwo : (2 : ENNReal) ≠ ⊤ := by simp
  have hnum : (2 * W) ≠ ⊤ := ENNReal.mul_ne_top htwo hW
  have hval : (2 * W / eta).toReal = 2 * W.toReal / eta.toReal := by
    rw [ENNReal.toReal_div, ENNReal.toReal_mul]
    norm_num
  rw [hval]
  have hpos : 0 < 2 * W.toReal := by linarith
  rw [div_eq_mul_inv, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) hW0.ne', Real.log_inv]
  have hinv : Real.log (1 / eta.toReal) = -Real.log eta.toReal := by
    rw [one_div, Real.log_inv]
  have : -Real.log eta.toReal ≤ Elog := by rw [← hinv]; exact hElog
  linarith

/-- **The `hsteps` shape, from a bound on the logarithm of the actual warm budget.**

This is the theorem the frontier's `hsteps` binder needs, and the one no file supplied.  Its
only non-structural input is `hWlog`, the compounding-budget bound. -/
theorem slowCanonicalSteps_le_ceil_of_log_le
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 < q) (hs0 : 0 < s0)
    {K : Set (EuclideanSpace Real (Fin n))} {retries : Nat → Nat}
    {eta zeta : Nat → ENNReal} {i : Nat}
    {Wlog Elog Zlog Ebound : Real}
    (hW : slowWarmBudget slowReferenceWarm n q s0 K retries i ≠ ⊤)
    (hW0 : 0 < (slowWarmBudget slowReferenceWarm n q s0 K retries i).toReal)
    (heta : eta i ≠ 0) (heta' : eta i ≠ ⊤)
    (hWlog : Real.log (slowWarmBudget slowReferenceWarm n q s0 K retries i).toReal ≤ Wlog)
    (hElog : Real.log (1 / (eta i).toReal) ≤ Elog)
    (hZlog : Real.log (1 / (zeta i).toReal) ≤ Zlog)
    (hE : slowActualDeadlineExpression n (radiusQDelta n q (slowSourceSigmaSq n s0 i))
      (slowSourceSigmaSq n s0 i) Wlog Elog Zlog ≤ Ebound) :
    slowCanonicalSteps slowReferenceWarm n q s0 K retries eta zeta i 0 ≤
      ⌈Ebound⌉₊ + 1 := by
  have hsigma : 0 ≤ slowSourceSigmaSq n s0 i :=
    (slowSourceSigmaSq_pos hn hs0 i).le
  have hdelta : radiusQDelta n q (slowSourceSigmaSq n s0 i) ≠ 0 :=
    (radiusQDelta_pos hn hq (slowSourceSigmaSq_pos hn hs0 i)).ne'
  have hlog := log_two_mul_div_le hW hW0 heta heta' hWlog hElog
  refine adjustableSpeedyDeadline_le_ceil_of_log_le hsigma hdelta hlog ?_
  refine le_trans ?_ hE
  unfold slowActualDeadlineExpression
  have hcoef : 0 ≤ 4 * 640 ^ 2 * slowSourceSigmaSq n s0 i * (n : Real) := by positivity
  have hden : 0 < (radiusQDelta n q (slowSourceSigmaSq n s0 i) * Real.log 2) ^ 2 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact pow_two_pos_of_ne_zero (mul_ne_zero hdelta hlog2.ne')
  gcongr

#print axioms slowActualDeadlineExpression
#print axioms log_two_mul_div_le
#print axioms slowCanonicalSteps_le_ceil_of_log_le

end Ttc.CVSlowActualDeadline
