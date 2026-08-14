import Ttc.Exec.CVHotRefreshRadialRuntime
import Ttc.Exec.CVGaussianScoreAwareSharpScheduleBound

/-!
# Adjustable mixing deadlines for independently refreshed hot seeds

The independent refresh prevents phase-to-phase warmness compounding.  This module
computes the literal logarithmic payload of `adjustableSpeedyDeadline` and substitutes
the moment-polynomial radial estimate from `CVHotRefreshRadialRuntime`.
-/

set_option autoImplicit false

namespace Ttc.CVHotRefreshDeadline

open Ttc.CVIndependentRefreshSeedLaws
open Ttc.CVHotRefreshRadialRuntime
open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVHybridSchedule
open Ttc.CVAdaptive
open scoped ENNReal

variable {n : Nat}

/-- Exact closed logarithmic payload for a refreshed hot seed and a positive score
share. -/
noncomputable def hotRefreshDeadlineLogEnvelope
    (n : Nat) (R s share : Real) : Real :=
  Real.log (hotRefreshWarmEnvelope n R s).toReal +
    Real.log 2 + 2 * Real.log 32 + 3 * Real.log (1 / share)

/-- The same payload after replacing the refresh logarithm by the public moment
polynomial bound. -/
noncomputable def hotRefreshRadialDeadlineLogEnvelope
    (n : Nat) (R2 eta share : Real) : Real :=
  1 / 32 + (n : Real) *
      Real.log (4 * max 1 (momentRefreshRadiusSqEnvelope n R2 eta)) +
    Real.log 2 + 2 * Real.log 32 + 3 * Real.log (1 / share)

/-- Natural deadline obtained by inserting the radial log envelope. -/
noncomputable def hotRefreshRadialDeadline
    (n : Nat) (delta sigmaSq R2 eta share : Real) : Nat :=
  ⌈4 * 640 ^ 2 * sigmaSq * (n : Real) *
      hotRefreshRadialDeadlineLogEnvelope n R2 eta share /
        (delta * Real.log 2) ^ 2 + 1⌉₊ + 1

/-- Algebraic identity for the score-aware adjustable-deadline logarithm. -/
theorem hotRefresh_deadlineLogPayload_eq
    (n : Nat) {R s share : Real} (hs : 0 < s) (hshare : 0 < share) :
    Real.log
        (((2 * hotRefreshWarmEnvelope n R s) /
          ENNReal.ofReal share).toReal) +
      2 * Real.log (1 / (ENNReal.ofReal (share / 32)).toReal) =
        hotRefreshDeadlineLogEnvelope n R s share := by
  have hwarm := hotRefreshWarmEnvelope_toReal_pos n (R := R) hs
  have hshare0 : 0 ≤ share := hshare.le
  have hshare32 : 0 ≤ share / 32 := by positivity
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hshare0, ENNReal.toReal_ofReal hshare32]
  have htwo : (2 : Real) ≠ 0 := by norm_num
  have hthirtytwo : (32 : Real) ≠ 0 := by norm_num
  have hwarm0 : (hotRefreshWarmEnvelope n R s).toReal ≠ 0 := hwarm.ne'
  have hshareNe : share ≠ 0 := hshare.ne'
  rw [Real.log_div (mul_ne_zero htwo hwarm0) hshareNe,
    Real.log_mul htwo hwarm0]
  have honeShare : (1 / share : Real) ≠ 0 := one_div_ne_zero hshareNe
  rw [show 1 / (share / 32) = 32 * (1 / share) by field_simp,
    Real.log_mul hthirtytwo honeShare]
  unfold hotRefreshDeadlineLogEnvelope
  simp only [one_div, Real.log_inv]
  ring

/-- At a hot phase of the public hybrid schedule, the literal payload is bounded by the
moment-polynomial radial expression. -/
theorem hotRefresh_scoreAware_deadlineLogPayload_le_radial
    (hn : 1 ≤ n) {m k i : Nat} {N s0 R2 eta eps : Real}
    {slack boundSq : Nat → Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hR2 : 0 < R2) (heta : 0 < eta) (heps : 0 < eps)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j)
    (hi : ¬ i < coldPhases n s0) :
    let R := markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n
    let s := sigmaSq n N s0 i
    let warm := hotRefreshWarmEnvelope n R s
    let share := scoreAwareShare m k eps slack boundSq i
    Real.log (((2 * warm) / scoreAwareEta m k eps slack boundSq i).toReal) +
        2 * Real.log (1 / (scoreAwareZeta m k eps slack boundSq i).toReal) ≤
      hotRefreshRadialDeadlineLogEnvelope n R2 eta share := by
  dsimp only
  let R := markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n
  let s := sigmaSq n N s0 i
  let share := scoreAwareShare m k eps slack boundSq i
  have hs : 0 < s := sigmaSq_pos hn hN hs0 i
  have hshare : 0 < share := scoreAwareShare_pos heps hslack hbound i
  change Real.log
      (((2 * hotRefreshWarmEnvelope n R s) / ENNReal.ofReal share).toReal) +
      2 * Real.log (1 / (ENNReal.ofReal (share / 32)).toReal) ≤ _
  rw [hotRefresh_deadlineLogPayload_eq n hs hshare]
  unfold hotRefreshDeadlineLogEnvelope hotRefreshRadialDeadlineLogEnvelope
  have hwarm := log_hotRefreshWarmEnvelope_momentPolynomial_hot_le
    hn hN hs0 hs01 hR2 heta hi
  linarith

/-- The actual score-aware adjustable deadline is bounded by the radial natural
deadline, phase by phase throughout the hot block. -/
theorem adjustableSpeedyDeadline_hotRefresh_le_radial
    (hn : 1 ≤ n) {m k i : Nat} {N s0 R2 eta eps delta : Real}
    {slack boundSq : Nat → Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hR2 : 0 < R2) (heta : 0 < eta) (heps : 0 < eps)
    (hdelta : delta ≠ 0)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j)
    (hi : ¬ i < coldPhases n s0) :
    let R := markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n
    adjustableSpeedyDeadline n delta (sigmaSq n N s0 i)
        ((2 * hotRefreshWarmEnvelope n R (sigmaSq n N s0 i)) /
          scoreAwareEta m k eps slack boundSq i)
        (scoreAwareZeta m k eps slack boundSq i) ≤
      hotRefreshRadialDeadline n delta (sigmaSq n N s0 i) R2 eta
        (scoreAwareShare m k eps slack boundSq i) := by
  dsimp only
  apply adjustableSpeedyDeadline_le_ceil_of_expression_le
  have hpayload := hotRefresh_scoreAware_deadlineLogPayload_le_radial
    (m := m) (k := k) hn hN hs0 hs01 hR2 heta heps hslack hbound hi
  have hsigma : 0 ≤ sigmaSq n N s0 i := (sigmaSq_pos hn hN hs0 i).le
  have hcoef : 0 ≤ 4 * 640 ^ 2 * sigmaSq n N s0 i * (n : Real) := by
    positivity
  have hden : 0 < (delta * Real.log 2) ^ 2 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact sq_pos_of_ne_zero (mul_ne_zero hdelta hlog2.ne')
  unfold adjustableSpeedyDeadlineExpression
  simpa only [add_comm] using add_le_add_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpayload hcoef) hden.le) 1

/-- Summed form of `adjustableSpeedyDeadline_hotRefresh_le_radial` over a hot
block.  This is the form used by the cost certificate: the independently
refreshed deadline can be replaced phase-by-phase without introducing a
warmness recurrence. -/
theorem sum_adjustableSpeedyDeadline_hotRefresh_le_radial
    (hn : 1 ≤ n) {m k hot : Nat} {N s0 R2 eta eps delta : Real}
    {slack boundSq : Nat → Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hR2 : 0 < R2) (heta : 0 < eta) (heps : 0 < eps)
    (hdelta : delta ≠ 0)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j) :
    let R := markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n
    ∑ q ∈ Finset.range hot,
        adjustableSpeedyDeadline n delta
          (sigmaSq n N s0 (coldPhases n s0 + q))
          ((2 * hotRefreshWarmEnvelope n R
              (sigmaSq n N s0 (coldPhases n s0 + q))) /
            scoreAwareEta m k eps slack boundSq (coldPhases n s0 + q))
          (scoreAwareZeta m k eps slack boundSq (coldPhases n s0 + q)) ≤
      ∑ q ∈ Finset.range hot,
        hotRefreshRadialDeadline n delta
          (sigmaSq n N s0 (coldPhases n s0 + q)) R2 eta
          (scoreAwareShare m k eps slack boundSq (coldPhases n s0 + q)) := by
  dsimp only
  apply Finset.sum_le_sum
  intro q hq
  exact adjustableSpeedyDeadline_hotRefresh_le_radial
    (m := m) (k := k) hn hN hs0 hs01 hR2 heta heps hdelta hslack hbound
      (by omega)

/-- Cost-weighted summed deadline comparison.  In particular, the operational
retry multiplicities may be kept verbatim while replacing every hot reset
deadline by its radial envelope. -/
theorem sum_retries_mul_adjustableSpeedyDeadline_hotRefresh_le_radial
    (hn : 1 ≤ n) {m k hot : Nat} {N s0 R2 eta eps delta : Real}
    {slack boundSq : Nat → Real} (retries : Nat → Nat)
    (hN : 0 < N) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hR2 : 0 < R2) (heta : 0 < eta) (heps : 0 < eps)
    (hdelta : delta ≠ 0)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j) :
    let R := markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n
    ∑ q ∈ Finset.range hot,
        retries (coldPhases n s0 + q) *
          adjustableSpeedyDeadline n delta
            (sigmaSq n N s0 (coldPhases n s0 + q))
            ((2 * hotRefreshWarmEnvelope n R
                (sigmaSq n N s0 (coldPhases n s0 + q))) /
              scoreAwareEta m k eps slack boundSq (coldPhases n s0 + q))
            (scoreAwareZeta m k eps slack boundSq (coldPhases n s0 + q)) ≤
      ∑ q ∈ Finset.range hot,
        retries (coldPhases n s0 + q) *
          hotRefreshRadialDeadline n delta
            (sigmaSq n N s0 (coldPhases n s0 + q)) R2 eta
            (scoreAwareShare m k eps slack boundSq (coldPhases n s0 + q)) := by
  dsimp only
  apply Finset.sum_le_sum
  intro q hq
  exact Nat.mul_le_mul_left _
    (adjustableSpeedyDeadline_hotRefresh_le_radial
      (m := m) (k := k) hn hN hs0 hs01 hR2 heta heps hdelta hslack hbound
        (by omega))

#print axioms hotRefresh_deadlineLogPayload_eq
#print axioms hotRefresh_scoreAware_deadlineLogPayload_le_radial
#print axioms adjustableSpeedyDeadline_hotRefresh_le_radial
#print axioms sum_adjustableSpeedyDeadline_hotRefresh_le_radial
#print axioms sum_retries_mul_adjustableSpeedyDeadline_hotRefresh_le_radial

end Ttc.CVHotRefreshDeadline
