import Ttc.Exec.CVSlowSourceReferenceCertificate
import Ttc.Exec.CVConcreteAugmentedRetryCutoffBudget

/-!
# Explicit retained-reference cost envelope for the slow source schedule

The retained reference has the fixed warmness `2e`; it never pays the possibly large
actual-path warmness.  Consequently any uniform bounds `T` and `L` on the literal phase
deadline and retry count give the elementary polynomial envelope

`k * m * 10 * L * T * (2e)`.

This file isolates exactly what remains to compare with the public source runtime: lower
bounds on the concrete score/moment shares (which imply `T,L` bounds) and a final scalar
inequality.  With arbitrary positive `slack` and `boundSq`, such lower bounds are not
available.
-/

set_option autoImplicit false

namespace Ttc.CVSlowSourceCostEnvelope

open Finset
open Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVSourcePolynomialCutoffCapstone
open scoped ENNReal BigOperators

/-- One slow retained-reference phase under uniform deadline and retry bounds. -/
theorem slowPhaseCostBound_le_uniform
    {n m k : Nat} {q eps : Real} {slack boundSq : Nat -> Real}
    {T L : Nat}
    (hsteps : forall i, slowScoreAwareSteps n m k q eps slack boundSq i 0 <= T)
    (hretries : forall i, scoreAwareRetries m k eps slack boundSq i <= L)
    (i : Nat) :
    slowPhaseCostBound n m k q eps slack boundSq i <=
      ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) := by
  unfold slowPhaseCostBound
  split
  · apply ENNReal.ofReal_le_ofReal
    have hmean := retryReferenceMeanEnvelope_le_uniform
      (M := 2 * Real.exp 1) (steps := fun _ =>
        slowScoreAwareSteps n m k q eps slack boundSq i 0)
      (L := scoreAwareRetries m k eps slack boundSq i) (T := T)
      (by positivity) (fun _ _ => hsteps i)
    calc
      retryReferenceMeanEnvelope (2 * Real.exp 1)
          (slowScoreAwareSteps n m k q eps slack boundSq i)
          (scoreAwareRetries m k eps slack boundSq i) =
          retryReferenceMeanEnvelope (2 * Real.exp 1)
            (fun _ => slowScoreAwareSteps n m k q eps slack boundSq i 0)
            (scoreAwareRetries m k eps slack boundSq i) := by rfl
      _ <= 10 * (scoreAwareRetries m k eps slack boundSq i : Real) *
          (T : Real) * (2 * Real.exp 1) := hmean
      _ <= 10 * (L : Real) * (T : Real) * (2 * Real.exp 1) := by
        have hL : (scoreAwareRetries m k eps slack boundSq i : Real) <= L := by
          exact_mod_cast hretries i
        gcongr
  · exact bot_le

/-- Sum over all slow phases. -/
theorem sum_slowPhaseCostBound_le_uniform
    {n m k : Nat} {q eps : Real} {slack boundSq : Nat -> Real}
    {T L : Nat}
    (hsteps : forall i, slowScoreAwareSteps n m k q eps slack boundSq i 0 <= T)
    (hretries : forall i, scoreAwareRetries m k eps slack boundSq i <= L) :
    (∑ i ∈ range m, slowPhaseCostBound n m k q eps slack boundSq i) <=
      (m : ENNReal) *
        ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) := by
  calc
    (∑ i ∈ range m, slowPhaseCostBound n m k q eps slack boundSq i) <=
        ∑ _i ∈ range m,
          ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) := by
      apply sum_le_sum
      intro i _
      exact slowPhaseCostBound_le_uniform hsteps hretries i
    _ = (m : ENNReal) *
        ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) := by
      simp [nsmul_eq_mul]

/-- The exact `k`-stream polynomial envelope consumed by the slow source certificate. -/
theorem aggregate_slowPhaseCostBound_le_uniform
    {n m k : Nat} {q eps : Real} {slack boundSq : Nat -> Real}
    {T L : Nat}
    (hsteps : forall i, slowScoreAwareSteps n m k q eps slack boundSq i 0 <= T)
    (hretries : forall i, scoreAwareRetries m k eps slack boundSq i <= L) :
    (k : ENNReal) *
        (∑ i ∈ range m, slowPhaseCostBound n m k q eps slack boundSq i) <=
      (k : ENNReal) * (m : ENNReal) *
        ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) := by
  calc
    (k : ENNReal) *
        (∑ i ∈ range m, slowPhaseCostBound n m k q eps slack boundSq i) <=
      (k : ENNReal) * ((m : ENNReal) *
        ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1))) := by
          gcongr
          exact sum_slowPhaseCostBound_le_uniform hsteps hretries
    _ = (k : ENNReal) * (m : ENNReal) *
        ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) := by
      ac_rfl

/-- Plug-in form for the remaining `hbudget` premise of
`exists_sourceReferenceTVOneRunCertificate_slowSource`.  After deadline and retry bounds
are supplied, only the displayed scalar comparison with the public source envelope
remains. -/
theorem slowSourceBudget_of_uniform
    {n m k : Nat} {q eps : Real} {slack boundSq : Nat -> Real}
    {T L : Nat} {runtimeConstant R requested : Real}
    (hsteps : forall i, slowScoreAwareSteps n m k q eps slack boundSq i 0 <= T)
    (hretries : forall i, scoreAwareRetries m k eps slack boundSq i <= L)
    (hscalar : (k : ENNReal) * (m : ENNReal) *
        ENNReal.ofReal (10 * (L : Real) * (T : Real) * (2 * Real.exp 1)) <=
      sourceOneRunQueryBudget runtimeConstant n R requested) :
    (k : ENNReal) *
        (∑ i ∈ range m, slowPhaseCostBound n m k q eps slack boundSq i) <=
      sourceOneRunQueryBudget runtimeConstant n R requested :=
  (aggregate_slowPhaseCostBound_le_uniform hsteps hretries).trans hscalar

#print axioms slowPhaseCostBound_le_uniform
#print axioms sum_slowPhaseCostBound_le_uniform
#print axioms aggregate_slowPhaseCostBound_le_uniform
#print axioms slowSourceBudget_of_uniform

end Ttc.CVSlowSourceCostEnvelope
