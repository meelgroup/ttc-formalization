import Ttc.Exec.CVGaussianScoreAwareSharpScheduleBound

/-!
# Monotonicity of the adjustable speedy-Gaussian deadline in the warmness argument

The runtime assembly cannot supply the exact operational warmness `M` fed to
`Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline`: that warmness is a compounding
recursion and only an *envelope* for it is provable.  Since the deadline consumes `M`
only through `Real.log M.toReal`, an upper bound on that logarithm already suffices.

This file records that fact in the three shapes the cost accounting consumes — a
log-payload bound, plain `ENNReal` monotonicity in `M`, and a `Nat` cap — together with
a real-envelope companion turning the resulting `⌈·⌉₊ + 1` back into a real bound with
additive slack `2`.
-/

set_option autoImplicit false

namespace Ttc.CVSpeedyDeadlineMono

open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVGaussianScoreAwareSharpScheduleBound
open scoped ENNReal

/-- The real expression rounded by `adjustableSpeedyDeadline` is monotone in any upper
bound for `Real.log M.toReal`. -/
theorem adjustableSpeedyDeadlineExpression_le_of_log_le
    {n : Nat} {delta sigmaSq : Real} {M eta : ENNReal} {Lbound : Real}
    (hsigma : 0 ≤ sigmaSq) (hdelta : delta ≠ 0)
    (hlog : Real.log M.toReal ≤ Lbound) :
    adjustableSpeedyDeadlineExpression n delta sigmaSq M eta ≤
      4 * 640 ^ 2 * sigmaSq * (n : Real) *
        (Lbound + 2 * Real.log (1 / eta.toReal)) / (delta * Real.log 2) ^ 2 + 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hne : delta * Real.log 2 ≠ 0 := mul_ne_zero hdelta hlog2.ne'
  have hden : 0 < (delta * Real.log 2) ^ 2 := pow_two_pos_of_ne_zero hne
  have hcoef : (0 : Real) ≤ 4 * 640 ^ 2 * sigmaSq * (n : Real) := by positivity
  unfold adjustableSpeedyDeadlineExpression
  gcongr

/-- The log-payload form of the deadline bound: an upper bound on `Real.log M.toReal`
transfers to the deadline with the same syntactic shape. -/
theorem adjustableSpeedyDeadline_le_of_log_le
    {n : Nat} {delta sigmaSq : Real} {M eta : ENNReal} {Lbound : Real}
    (hsigma : 0 ≤ sigmaSq) (hdelta : delta ≠ 0)
    (hlog : Real.log M.toReal ≤ Lbound) :
    adjustableSpeedyDeadline n delta sigmaSq M eta ≤
      ⌈4 * 640 ^ 2 * sigmaSq * (n : Real) *
        (Lbound + 2 * Real.log (1 / eta.toReal)) / (delta * Real.log 2) ^ 2 + 1⌉₊ + 1 :=
  adjustableSpeedyDeadline_le_ceil_of_expression_le
    (adjustableSpeedyDeadlineExpression_le_of_log_le hsigma hdelta hlog)

/-- The `Nat`-cap corollary: any real cap for the log-payload expression caps the
deadline. -/
theorem adjustableSpeedyDeadline_le_ceil_of_log_le
    {n : Nat} {delta sigmaSq : Real} {M eta : ENNReal} {Lbound Ebound : Real}
    (hsigma : 0 ≤ sigmaSq) (hdelta : delta ≠ 0)
    (hlog : Real.log M.toReal ≤ Lbound)
    (hE : 4 * 640 ^ 2 * sigmaSq * (n : Real) *
        (Lbound + 2 * Real.log (1 / eta.toReal)) / (delta * Real.log 2) ^ 2 + 1 ≤ Ebound) :
    adjustableSpeedyDeadline n delta sigmaSq M eta ≤ ⌈Ebound⌉₊ + 1 :=
  adjustableSpeedyDeadline_le_ceil_of_expression_le
    ((adjustableSpeedyDeadlineExpression_le_of_log_le hsigma hdelta hlog).trans hE)

/-- Plain monotonicity in the warmness argument, for callers holding an `ENNReal`
bound rather than a logarithmic one. -/
theorem adjustableSpeedyDeadline_mono_warm
    {n : Nat} {delta sigmaSq : Real} {M M' eta : ENNReal}
    (hsigma : 0 ≤ sigmaSq) (hdelta : delta ≠ 0)
    (hM : 1 ≤ M) (hM' : M' ≠ ⊤) (hle : M ≤ M') :
    adjustableSpeedyDeadline n delta sigmaSq M eta ≤
      adjustableSpeedyDeadline n delta sigmaSq M' eta := by
  have hMtop : M ≠ ⊤ := ne_top_of_le_ne_top hM' hle
  have hMreal : 1 ≤ M.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hMtop hM
  have hMpos : 0 < M.toReal := lt_of_lt_of_le zero_lt_one hMreal
  have hlog : Real.log M.toReal ≤ Real.log M'.toReal :=
    Real.log_le_log hMpos (ENNReal.toReal_mono hM' hle)
  have := adjustableSpeedyDeadline_le_of_log_le (n := n) (eta := eta) hsigma hdelta hlog
  rw [adjustableSpeedyDeadline]
  exact this

/-- Real-envelope companion: the `Nat` produced by a ceiling deadline bound is itself
bounded by the underlying real with additive slack `2`. -/
theorem cast_ceil_add_one_le (E : Real) (hE : 0 ≤ E) :
    ((⌈E⌉₊ + 1 : Nat) : Real) ≤ E + 2 := by
  have h := (Nat.ceil_lt_add_one hE).le
  push_cast
  linarith

#print axioms adjustableSpeedyDeadlineExpression_le_of_log_le
#print axioms adjustableSpeedyDeadline_le_of_log_le
#print axioms adjustableSpeedyDeadline_le_ceil_of_log_le
#print axioms adjustableSpeedyDeadline_mono_warm
#print axioms cast_ceil_add_one_le

end Ttc.CVSpeedyDeadlineMono
