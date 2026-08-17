import Ttc.Exec.CVSlowCanonicalAccuracyBudget

/-!
# Strict bounds on the slow schedule's realised accuracy

`Ttc.CVSlowCanonicalAccuracyBudget` bounds `slowAccuracyRequested` above by the target.  The
assembly needs three further facts about the *internal-half* instantiation
`eps := epsIn / 2`, and all three are strict where the existing bounds are not:

* `0 < requested` and `requested < 1` — side conditions of the cost lemmas, which cannot be
  read off `requested ≤ epsIn` when `epsIn = 1`;
* `epsIn / 2 ≤ requested` — the hypothesis `he` of
  `Ttc.CVBudgetEpsAbsorb.sourceOneRunQueryBudget_absorb`, which is what lets the accuracy
  slot move from the realised `requested` to the requested `epsIn` at an absolute constant.

The last one is why the construction is run at exactly half the target accuracy rather than
at some smaller fraction: any fixed fraction would do, and `1/2` keeps the absorbed constant
at `64`.
-/

set_option autoImplicit false

namespace Ttc.CVSlowAccuracyStrict

open Ttc.CVSlowCanonicalAccuracyBudget
open Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVCorrectedRuntime

/-- The realised accuracy is at least the internal accuracy it was run at. -/
theorem half_le_slowAccuracyRequested (m k : Nat) {epsIn : Real} (heps : 0 < epsIn) :
    epsIn / 2 ≤ slowAccuracyRequested m k (epsIn / 2) := by
  have hhalf : 0 < epsIn / 2 := by linarith
  have hbeta : 0 ≤ scoreAwareAccuracyBeta m k (epsIn / 2) :=
    scoreAwareAccuracyBeta_nonneg m k hhalf
  have hprod : 0 ≤ epsIn / 2 * scoreAwareAccuracyBeta m k (epsIn / 2) :=
    mul_nonneg hhalf.le hbeta
  unfold slowAccuracyRequested
  linarith

/-- The realised accuracy is positive. -/
theorem slowAccuracyRequested_half_pos (m k : Nat) {epsIn : Real} (heps : 0 < epsIn) :
    0 < slowAccuracyRequested m k (epsIn / 2) := by
  have h := half_le_slowAccuracyRequested m k heps
  linarith

/-- **The realised accuracy is strictly below one**, even at `epsIn = 1`.

This is what the half buys: at the canonical stream count the realised accuracy is at most
`11/16` of the target, so the strict inequality survives the boundary case that
`slowAccuracyRequested_le_of_half`'s non-strict `≤ epsIn` does not. -/
theorem slowAccuracyRequested_half_lt_one (m : Nat) {epsIn : Real}
    (heps : 0 < epsIn) (heps1 : epsIn ≤ 1) :
    slowAccuracyRequested m (correctedRuntimeSamples m (epsIn / 2)) (epsIn / 2) < 1 := by
  have hhalf : 0 < epsIn / 2 := by linarith
  have hhalf1 : epsIn / 2 ≤ 1 := by linarith
  have h := slowAccuracyRequested_canonical_le m hhalf hhalf1
  have hq : epsIn / 2 + (epsIn / 2) / 4 + (epsIn / 2) * ((epsIn / 2) / 4) < 1 := by
    nlinarith [sq_nonneg epsIn]
  linarith

/-- The realised accuracy is under the target, restated here so a caller needs one import. -/
theorem slowAccuracyRequested_half_le (m : Nat) {epsIn : Real}
    (heps : 0 < epsIn) (heps1 : epsIn ≤ 1) :
    slowAccuracyRequested m (correctedRuntimeSamples m (epsIn / 2)) (epsIn / 2) ≤ epsIn :=
  slowAccuracyRequested_le_of_half m heps heps1

#print axioms half_le_slowAccuracyRequested
#print axioms slowAccuracyRequested_half_pos
#print axioms slowAccuracyRequested_half_lt_one
#print axioms slowAccuracyRequested_half_le

end Ttc.CVSlowAccuracyStrict
