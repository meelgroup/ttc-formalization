/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CVPerPhaseSamples
import Ttc.Exec.CVSlowAccuracyStrict

/-!
# Parameter-level re-proofs at the per-phase stream count (P2)

`Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples n m eps = ⌈100000·(m+n)/(n·eps²)⌉₊ + 1`
shrinks the canonical stream count `Ttc.CVCorrectedRuntime.correctedRuntimeSamples m eps
= ⌈100000·(m+1)/eps²⌉₊ + 1` by a factor `n`.  A *smaller* `k` makes

* `Ttc.CVGaussianBlockRetryParameters.blockShare m k eps = correctedNu m eps / (8(k+1))`
  **larger** (it is decreasing in `k`), hence
* `scoreAwareMeanEta = √((7/5)·blockShare)` larger, hence
* `scoreAwareMeanGamma = 2m·scoreAwareMeanEta` larger, by a factor `√n`.

The larger share is good for the retry cap and the deadline; the larger gamma eats
accuracy budget.  This file re-checks the accuracy side and records the share payoff.

## The verdict

**Every accuracy bound survives, with no hypothesis on `n` at all.**  In fact the bounds
are *`k`-free*: they hold for every `k : Nat`, including `k = 0`.  The reason is an exact
computation the original proof never performed.  Writing `α = correctedAlpha m eps =
10⁵(m+1)/eps²`,

  `correctedNu m eps = eps²/(10⁵·α⁴·(m+1)) = eps¹⁰/(10²⁵·(m+1)⁵)`

(`correctedNu_eq` below).  The old proof
`Ttc.CVGaussianScoreAwareMeanBudget.scoreAwareMeanGamma_corrected_le_div_hundred`
discarded `α⁴ ≥ 1` and then spent the sample budget to buy a second factor `10⁵(m+1)`
out of `blockShare`'s denominator.  Keeping `α⁴` instead gives

  `gamma² = 4m²·(7/5)·blockShare ≤ (7/10)·m²·eps¹⁰/(10²⁵·(m+1)⁵) ≤ (7/10)·eps²/10²⁵`,

since `m² ≤ (m+1)⁵` and `eps¹⁰ ≤ eps²`.  That is below `(eps/100)²` by twenty-one orders
of magnitude, and `k` never appears.  So the extraction of `100000·(m+1) ≤ k` at
`CVGaussianScoreAwareMeanBudget.lean:69-74` was pure slack, exactly as P2's audit
predicted: `k ≥ 0` suffices, let alone `k ≥ 1`.

## Contents

* `correctedNu_eq` — the exact closed form of `correctedNu`.
* `scoreAwareMeanGamma_le_div_hundred` / `_le_one` — `k`-free gamma bounds, and their
  instantiations `scoreAwareMeanGamma_perPhase_le` / `_perPhase_le_one`.
* `scoreAwareAccuracyBeta_le` (`≤ eps/4`, `k`-free) and
  `scoreAwareAccuracyBeta_perPhase_le`.
* the `slowAccuracyRequested` consequences at the per-phase count: `_perPhase_le`,
  `_perPhase_le_two`, `_perPhase_le_of_half`, and the strictness facts
  `_perPhase_half_pos`, `_perPhase_half_lt_one`, `_perPhase_half_le`.
* `blockShare_perPhase_ge` — the second, independent win: the smaller stream count
  *raises* the share floor.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVPerPhaseParameters

open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVContinuingRetryParameters
open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVSlowCanonicalAccuracyBudget
open Ttc.CVPerPhaseSamples

/-! ## The exact value of the corrected mixing share -/

/-- **`correctedNu` in closed form.**  Substituting `correctedAlpha m eps =
10⁵(m+1)/eps²` into `correctedNu m eps = eps²/(10⁵·correctedAlpha⁴·(m+1))` and clearing
the nested fraction gives a pure `Θ(eps¹⁰/m⁵)`.  The `eps⁸` released by `α⁴` is the
budget the old gamma proof threw away. -/
theorem correctedNu_eq (m : Nat) {eps : Real} (heps : 0 < eps) :
    correctedNu m eps = eps ^ 10 / (10 ^ 25 * ((m : Real) + 1) ^ 5) := by
  have hm : ((m : Real) + 1) ≠ 0 := by positivity
  have he : eps ≠ 0 := ne_of_gt heps
  rw [correctedNu, correctedAlpha]
  field_simp
  ring

/-- `blockShare` is decreasing in the stream count, so dropping `k` to zero is the
worst case for every accuracy bound that consumes it. -/
theorem blockShare_le_nu_div_eight (m k : Nat) (eps : Real) :
    blockShare m k eps ≤ correctedNu m eps / 8 := by
  have hnu0 : (0 : Real) ≤ correctedNu m eps := correctedNu_nonneg
  have hk : (8 : Real) ≤ 8 * ((k : Real) + 1) := by
    have : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
    nlinarith
  rw [blockShare]
  exact div_le_div_of_nonneg_left hnu0 (by norm_num) hk

/-! ## The `k`-free gamma bound -/

/-- **The aggregate mean bias is at most one percent of the accuracy, at every stream
count.**  This is the sharp form of
`Ttc.CVGaussianScoreAwareMeanBudget.scoreAwareMeanGamma_corrected_le_div_hundred`: no
sample budget, no positivity of `k`, no constraint on `n`. -/
theorem scoreAwareMeanGamma_le_div_hundred (m k : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareMeanGamma m k eps ≤ eps / 100 := by
  have hx0 : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have hx1 : (1 : Real) ≤ (m : Real) + 1 := by linarith
  have he2 : (0 : Real) < eps ^ 2 := by positivity
  have he2le : eps ^ 2 ≤ 1 := by nlinarith
  -- `eps ^ 10 ≤ eps ^ 2`
  have hpow : eps ^ 10 ≤ eps ^ 2 := by
    have h4 : (eps ^ 2) ^ 4 ≤ 1 := by
      calc (eps ^ 2) ^ 4 ≤ 1 ^ 4 := by gcongr
        _ = 1 := by norm_num
    calc eps ^ 10 = eps ^ 2 * (eps ^ 2) ^ 4 := by ring
      _ ≤ eps ^ 2 * 1 := by gcongr
      _ = eps ^ 2 := by ring
  -- `m ^ 2 ≤ (m + 1) ^ 5`
  have hmpow : (m : Real) ^ 2 ≤ ((m : Real) + 1) ^ 5 := by
    have h25 : ((m : Real) + 1) ^ 2 ≤ ((m : Real) + 1) ^ 5 :=
      pow_le_pow_right₀ hx1 (by norm_num)
    nlinarith
  have hden : (0 : Real) < 10 ^ 25 * ((m : Real) + 1) ^ 5 := by positivity
  have hb0 : (0 : Real) ≤ blockShare m k eps := (blockShare_pos heps).le
  -- the share bound in closed form
  have hb : blockShare m k eps ≤ eps ^ 10 / (8 * (10 ^ 25 * ((m : Real) + 1) ^ 5)) := by
    have h := blockShare_le_nu_div_eight m k eps
    rw [correctedNu_eq m heps] at h
    calc blockShare m k eps
        ≤ eps ^ 10 / (10 ^ 25 * ((m : Real) + 1) ^ 5) / 8 := h
      _ = eps ^ 10 / (8 * (10 ^ 25 * ((m : Real) + 1) ^ 5)) := by
          rw [div_div]; ring_nf
  -- the squared bound
  have hsmall : 4 * (m : Real) ^ 2 * ((7 / 5 : Real) * blockShare m k eps)
      ≤ eps ^ 2 / 10000 := by
    have hstep : 4 * (m : Real) ^ 2 * ((7 / 5 : Real) * blockShare m k eps)
        ≤ 4 * (m : Real) ^ 2 *
          ((7 / 5 : Real) * (eps ^ 10 / (8 * (10 ^ 25 * ((m : Real) + 1) ^ 5)))) := by
      gcongr
    refine hstep.trans ?_
    have h5 : ((m : Real) + 1) ^ 5 ≠ 0 := by positivity
    have hkey : (m : Real) ^ 2 * eps ^ 10
        ≤ ((m : Real) + 1) ^ 5 * eps ^ 2 := by
      have h1 : (m : Real) ^ 2 * eps ^ 10 ≤ (m : Real) ^ 2 * eps ^ 2 := by
        gcongr
      have h2 : (m : Real) ^ 2 * eps ^ 2 ≤ ((m : Real) + 1) ^ 5 * eps ^ 2 := by
        gcongr
      linarith
    calc 4 * (m : Real) ^ 2 *
          ((7 / 5 : Real) * (eps ^ 10 / (8 * (10 ^ 25 * ((m : Real) + 1) ^ 5))))
        = (28 / 5 : Real) * ((m : Real) ^ 2 * eps ^ 10) /
            (8 * (10 ^ 25 * ((m : Real) + 1) ^ 5)) := by ring
      _ ≤ (28 / 5 : Real) * (((m : Real) + 1) ^ 5 * eps ^ 2) /
            (8 * (10 ^ 25 * ((m : Real) + 1) ^ 5)) := by gcongr
      _ = (28 / 5 : Real) * eps ^ 2 / (8 * 10 ^ 25) := by
            field_simp
      _ ≤ eps ^ 2 / 10000 := by nlinarith
  -- square roots
  have hsqrtSq : (scoreAwareMeanEta m k eps) ^ 2 = (7 / 5 : Real) * blockShare m k eps := by
    unfold scoreAwareMeanEta
    rw [Real.sq_sqrt]
    positivity
  have hgamma0 := scoreAwareMeanGamma_nonneg m k eps
  have hgammaSq : (scoreAwareMeanGamma m k eps) ^ 2 ≤ (eps / 100) ^ 2 := by
    calc (scoreAwareMeanGamma m k eps) ^ 2
        = 4 * (m : Real) ^ 2 * ((7 / 5 : Real) * blockShare m k eps) := by
          rw [scoreAwareMeanGamma, mul_pow, mul_pow, hsqrtSq]; ring
      _ ≤ eps ^ 2 / 10000 := hsmall
      _ = (eps / 100) ^ 2 := by ring
  nlinarith [sq_nonneg (scoreAwareMeanGamma m k eps + eps / 100)]

/-- The `k`-free analogue of
`Ttc.CVGaussianScoreAwareMeanBudget.scoreAwareMeanGamma_corrected_le_one`. -/
theorem scoreAwareMeanGamma_le_one (m k : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareMeanGamma m k eps ≤ 1 := by
  have h := scoreAwareMeanGamma_le_div_hundred m k heps heps1
  linarith

/-! ## Deliverable 1 and 2 — the gamma bounds at the per-phase stream count -/

/-- **Deliverable 1.**  The aggregate mean bias at the per-phase stream count is at most
`eps/100` — the *same* constant the canonical count achieves.  No hypothesis on `n`. -/
theorem scoreAwareMeanGamma_perPhase_le (n m : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareMeanGamma m (perPhaseRuntimeSamples n m eps) eps ≤ eps / 100 :=
  scoreAwareMeanGamma_le_div_hundred m (perPhaseRuntimeSamples n m eps) heps heps1

/-- **Deliverable 2.**  The analogue of `scoreAwareMeanGamma_corrected_le_one`, proved
without any sample-budget extraction at all. -/
theorem scoreAwareMeanGamma_perPhase_le_one (n m : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareMeanGamma m (perPhaseRuntimeSamples n m eps) eps ≤ 1 :=
  scoreAwareMeanGamma_le_one m (perPhaseRuntimeSamples n m eps) heps heps1

/-- The `eps/8` form the accuracy budget consumes. -/
theorem scoreAwareMeanGamma_perPhase_le_div_eight (n m : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareMeanGamma m (perPhaseRuntimeSamples n m eps) eps ≤ eps / 8 := by
  have h := scoreAwareMeanGamma_perPhase_le n m heps heps1
  linarith

/-! ## Deliverable 3 — the accuracy budget at the per-phase stream count -/

/-- The `k`-free analogue of
`Ttc.CVSlowCanonicalAccuracyBudget.scoreAwareAccuracyBeta_canonical_le`. -/
theorem scoreAwareAccuracyBeta_le (m k : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareAccuracyBeta m k eps ≤ eps / 4 := by
  have htheta : (m : Real) / (2 * correctedAlpha m eps) ≤ eps ^ 2 / 200000 :=
    phase_div_two_correctedAlpha_le m heps
  have halpha : 0 < correctedAlpha m eps := correctedAlpha_pos heps
  have htheta0 : 0 ≤ (m : Real) / (2 * correctedAlpha m eps) :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hgamma : scoreAwareMeanGamma m k eps ≤ eps / 8 := by
    have h := scoreAwareMeanGamma_le_div_hundred m k heps heps1
    linarith
  have hgamma0 : 0 ≤ scoreAwareMeanGamma m k eps := scoreAwareMeanGamma_nonneg m k eps
  have hprod : ((m : Real) / (2 * correctedAlpha m eps)) * scoreAwareMeanGamma m k eps ≤
      (eps ^ 2 / 200000) * (eps / 8) :=
    mul_le_mul htheta hgamma hgamma0 (by positivity)
  have hsq : eps ^ 2 ≤ eps := by nlinarith
  have hcube : eps ^ 2 * eps ≤ eps := by nlinarith
  unfold scoreAwareAccuracyBeta
  calc
    (m : Real) / (2 * correctedAlpha m eps) + scoreAwareMeanGamma m k eps +
        ((m : Real) / (2 * correctedAlpha m eps)) * scoreAwareMeanGamma m k eps ≤
        eps ^ 2 / 200000 + eps / 8 + (eps ^ 2 / 200000) * (eps / 8) := by
      gcongr
    _ ≤ eps / 4 := by nlinarith

/-- **Deliverable 3.**  At the per-phase stream count the whole score-aware allowance
still costs at most a quarter of the accuracy — the same constant as at the canonical
count, with no hypothesis on `n`. -/
theorem scoreAwareAccuracyBeta_perPhase_le (n m : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    scoreAwareAccuracyBeta m (perPhaseRuntimeSamples n m eps) eps ≤ eps / 4 :=
  scoreAwareAccuracyBeta_le m (perPhaseRuntimeSamples n m eps) heps heps1

/-- The canonical request at the per-phase stream count. -/
theorem slowAccuracyRequested_perPhase_le (n m : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    slowAccuracyRequested m (perPhaseRuntimeSamples n m eps) eps ≤
      eps + eps / 4 + eps * (eps / 4) := by
  have hbeta := scoreAwareAccuracyBeta_perPhase_le n m heps heps1
  unfold slowAccuracyRequested
  gcongr

/-- Hence the per-phase request never exceeds twice the internal accuracy. -/
theorem slowAccuracyRequested_perPhase_le_two (n m : Nat) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    slowAccuracyRequested m (perPhaseRuntimeSamples n m eps) eps ≤ 2 * eps := by
  have h := slowAccuracyRequested_perPhase_le n m heps heps1
  nlinarith

/-- Consumer-facing form: running the construction at internal accuracy `epsIn / 2` with
per-phase provisioning meets the externally requested accuracy `epsIn`. -/
theorem slowAccuracyRequested_perPhase_le_of_half (n m : Nat) {epsIn : Real}
    (heps : 0 < epsIn) (heps1 : epsIn ≤ 1) :
    slowAccuracyRequested m (perPhaseRuntimeSamples n m (epsIn / 2)) (epsIn / 2) ≤
      epsIn := by
  have h := slowAccuracyRequested_perPhase_le_two n m
    (eps := epsIn / 2) (by positivity) (by linarith)
  linarith

/-! ### The strictness facts of `Ttc.CVSlowAccuracyStrict` at the per-phase count

`Ttc.CVSlowAccuracyStrict.half_le_slowAccuracyRequested` and
`Ttc.CVSlowAccuracyStrict.slowAccuracyRequested_half_pos` are already stated for a
general stream count, so they instantiate directly.  Only the two facts that mention
`correctedRuntimeSamples` need per-phase versions. -/

/-- The realised accuracy at the per-phase count is at least the internal accuracy. -/
theorem half_le_slowAccuracyRequested_perPhase (n m : Nat) {epsIn : Real}
    (heps : 0 < epsIn) :
    epsIn / 2 ≤
      slowAccuracyRequested m (perPhaseRuntimeSamples n m (epsIn / 2)) (epsIn / 2) :=
  Ttc.CVSlowAccuracyStrict.half_le_slowAccuracyRequested m
    (perPhaseRuntimeSamples n m (epsIn / 2)) heps

/-- The realised accuracy at the per-phase count is positive. -/
theorem slowAccuracyRequested_perPhase_half_pos (n m : Nat) {epsIn : Real}
    (heps : 0 < epsIn) :
    0 < slowAccuracyRequested m (perPhaseRuntimeSamples n m (epsIn / 2)) (epsIn / 2) :=
  Ttc.CVSlowAccuracyStrict.slowAccuracyRequested_half_pos m
    (perPhaseRuntimeSamples n m (epsIn / 2)) heps

/-- The realised accuracy at the per-phase count is strictly below one, even at
`epsIn = 1`. -/
theorem slowAccuracyRequested_perPhase_half_lt_one (n m : Nat) {epsIn : Real}
    (heps : 0 < epsIn) (heps1 : epsIn ≤ 1) :
    slowAccuracyRequested m (perPhaseRuntimeSamples n m (epsIn / 2)) (epsIn / 2) < 1 := by
  have hhalf : 0 < epsIn / 2 := by linarith
  have hhalf1 : epsIn / 2 ≤ 1 := by linarith
  have h := slowAccuracyRequested_perPhase_le n m hhalf hhalf1
  have hq : epsIn / 2 + (epsIn / 2) / 4 + (epsIn / 2) * ((epsIn / 2) / 4) < 1 := by
    nlinarith [sq_nonneg epsIn]
  linarith

/-- The realised accuracy at the per-phase count is under the target. -/
theorem slowAccuracyRequested_perPhase_half_le (n m : Nat) {epsIn : Real}
    (heps : 0 < epsIn) (heps1 : epsIn ≤ 1) :
    slowAccuracyRequested m (perPhaseRuntimeSamples n m (epsIn / 2)) (epsIn / 2) ≤
      epsIn :=
  slowAccuracyRequested_perPhase_le_of_half n m heps heps1

/-! ## Deliverable 4 — the share payoff -/

/-- `blockShare` is antitone in the stream count. -/
theorem blockShare_antitone {m k l : Nat} {eps : Real} (hkl : k ≤ l) :
    blockShare m l eps ≤ blockShare m k eps := by
  have hnu0 : (0 : Real) ≤ correctedNu m eps := correctedNu_nonneg
  have hklR : (k : Real) ≤ (l : Real) := by exact_mod_cast hkl
  have hk0 : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
  rw [blockShare, blockShare]
  exact div_le_div_of_nonneg_left hnu0 (by positivity) (by linarith)

/-- **Deliverable 4 — the second, independent win.**  The per-phase stream count is at
most the canonical one, and `blockShare` is decreasing in the count, so per-phase
provisioning *raises* the share floor.  Downstream this lowers
`Ttc.CVGaussianBlockRetryParameters.blockRetries` (the retry cap is a dyadic tail index
of the share) and shrinks the deadline payload, at no accuracy cost — the accuracy
bounds above are `k`-free.

The hypotheses are exactly those of
`Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples_le_correctedRuntimeSamples`, and they are
free in the canonical slow regime, where `m = slowCanonicalPhases n R2 ≈ n·log(nR²) ≥ n`
(see `Ttc/Exec/CVPerPhaseSamples.lean:337-342`). -/
theorem blockShare_perPhase_ge {n m : Nat} {eps : Real}
    (hn : 3 ≤ n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    blockShare m (correctedRuntimeSamples m eps) eps ≤
      blockShare m (perPhaseRuntimeSamples n m eps) eps :=
  blockShare_antitone
    (perPhaseRuntimeSamples_le_correctedRuntimeSamples hn hnm heps heps1)

/-- **The share payoff, quantified.**  The per-phase share floor is at least `n/6` times
the canonical one:

  `n · blockShare m (correctedRuntimeSamples m eps) eps ≤
     6 · blockShare m (perPhaseRuntimeSamples n m eps) eps`.

This is the exact numerical counterpart of
`Ttc.CVPerPhaseSamples.perPhaseRuntimeSamples_saving` (`n·new ≤ 3·old`) transported
through `blockShare`'s reciprocal, and it holds in the same regime `n ≤ m+1`.  It is the
`√n` factor of the introduction, seen before the square root. -/
theorem nmul_blockShare_corrected_le {n m : Nat} {eps : Real}
    (hn : 0 < n) (hnm : (n : Real) ≤ (m : Real) + 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (n : Real) * blockShare m (correctedRuntimeSamples m eps) eps ≤
      6 * blockShare m (perPhaseRuntimeSamples n m eps) eps := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hnu0 : (0 : Real) ≤ correctedNu m eps := correctedNu_nonneg
  have hP0 : (0 : Real) ≤ (perPhaseRuntimeSamples n m eps : Real) := Nat.cast_nonneg _
  have hC0 : (0 : Real) ≤ (correctedRuntimeSamples m eps : Real) := Nat.cast_nonneg _
  have he2le : eps ^ 2 ≤ 1 := by nlinarith
  have hsav := perPhaseRuntimeSamples_saving hn hnm heps heps1
  -- the canonical count already dominates `n`
  have hnC : (n : Real) ≤ (correctedRuntimeSamples m eps : Real) := by
    have h := correctedRuntimeSamples_budget (m := m) (eps := eps) heps
    rw [Ttc.CVCorrected.CorrectedSampleBudget] at h
    nlinarith
  have hbound : (n : Real) * ((perPhaseRuntimeSamples n m eps : Real) + 1) ≤
      6 * ((correctedRuntimeSamples m eps : Real) + 1) := by nlinarith
  have hCden : (0 : Real) < 8 * ((correctedRuntimeSamples m eps : Real) + 1) := by
    positivity
  have hPden : (0 : Real) < 8 * ((perPhaseRuntimeSamples n m eps : Real) + 1) := by
    positivity
  rw [blockShare, blockShare, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff₀ hCden hPden]
  nlinarith [mul_le_mul_of_nonneg_left hbound hnu0]

#print axioms correctedNu_eq
#print axioms blockShare_le_nu_div_eight
#print axioms scoreAwareMeanGamma_le_div_hundred
#print axioms scoreAwareMeanGamma_le_one
#print axioms scoreAwareMeanGamma_perPhase_le
#print axioms scoreAwareMeanGamma_perPhase_le_one
#print axioms scoreAwareMeanGamma_perPhase_le_div_eight
#print axioms scoreAwareAccuracyBeta_le
#print axioms scoreAwareAccuracyBeta_perPhase_le
#print axioms slowAccuracyRequested_perPhase_le
#print axioms slowAccuracyRequested_perPhase_le_two
#print axioms slowAccuracyRequested_perPhase_le_of_half
#print axioms half_le_slowAccuracyRequested_perPhase
#print axioms slowAccuracyRequested_perPhase_half_pos
#print axioms slowAccuracyRequested_perPhase_half_lt_one
#print axioms slowAccuracyRequested_perPhase_half_le
#print axioms blockShare_antitone
#print axioms blockShare_perPhase_ge
#print axioms nmul_blockShare_corrected_le

end Ttc.CVPerPhaseParameters
