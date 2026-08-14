import Ttc.Volume.CVCorrectedLogarithmicRadiusRuntime
import Ttc.Exec.CVHotRefreshHonestRuntime
import Ttc.Exec.CVColdActualWarmReferenceCostArithmetic

/-!
# Global adjustable radius for hybrid operational tails

A fixed radius-four truncation spends a fixed positive tail at every phase and therefore
cannot support an unbounded number of hot phases.  The logarithmic adjustable selector
instead allocates one tail budget across all phase/stream calls.  This file records both
the exact accumulated-tail statement and the cold-block mixing coefficient of that
selector.
-/

set_option autoImplicit false

namespace Ttc.CVGlobalAdjustableRadiusAudit

open Arlib.GaussianCooling
open Ttc.CVAdaptive
open Ttc.CVCorrectedRuntime
open Ttc.CVHotRefreshHonestRuntime
open Ttc.CVColdActualWarmReferenceCostArithmetic
open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVGaussianColdHotRecursiveStep
open Ttc.CVWarmBudgetRecurrence
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVCorrectedFixedBlockCost
open scoped ENNReal

/-- A fixed radius-four tail cannot fit any fixed positive global budget for arbitrarily
many active calls.  This is the precise obstruction to using the same per-phase tail
after the hot phase count becomes input-dependent. -/
theorem exists_activeCalls_radiusFour_tail_gt
    (n : Nat) {k : Nat} (hk : 0 < k) {b : Real} (hb : 0 < b) :
    ∃ m : Nat, b < ((m * k : Nat) : Real) *
      (4 * Real.exp (-(15 : Real) / 2)) ^ n := by
  let t : Real := (4 * Real.exp (-(15 : Real) / 2)) ^ n
  have ht : 0 < t := by dsimp only [t]; positivity
  have hkt : 0 < (k : Real) * t := mul_pos (by exact_mod_cast hk) ht
  obtain ⟨m, hm⟩ := exists_nat_gt (b / ((k : Real) * t))
  refine ⟨m, ?_⟩
  have hmul : b < (m : Real) * ((k : Real) * t) :=
    (div_lt_iff₀ hkt).mp hm
  dsimp only [t] at hmul ⊢
  push_cast
  simpa only [mul_assoc] using hmul

/-- The selected global radius spends at most `1/20` across every call in a run. -/
theorem correctedLogarithmicQ_totalTail_le
    {n m k : Nat} (hn : 1 ≤ n) (hk : 0 < k) :
    runwiseSamplerCalls m k *
        (correctedLogarithmicQ n m k *
          Real.exp (-(correctedLogarithmicQ n m k ^ 2 - 1) / 2)) ^ n ≤
      1 / 20 := by
  exact (correctedLogarithmicQ_tailFits hn hk).2

/-- Consequently, the `m*k` active phase/stream calls fit the same budget; the extra
`+1` in `runwiseSamplerCalls` is harmless slack. -/
theorem activeCalls_correctedLogarithmicQ_totalTail_le
    {n m k : Nat} (hn : 1 ≤ n) (hk : 0 < k) :
    ((m * k : Nat) : Real) *
        (correctedLogarithmicQ n m k *
          Real.exp (-(correctedLogarithmicQ n m k ^ 2 - 1) / 2)) ^ n ≤
      1 / 20 := by
  have htail0 : 0 ≤
      (correctedLogarithmicQ n m k *
        Real.exp (-(correctedLogarithmicQ n m k ^ 2 - 1) / 2)) ^ n := by
    have hq : 0 < correctedLogarithmicQ n m k :=
      lt_trans (by norm_num) (correctedLogarithmicQ_tailFits hn hk).1
    positivity
  apply (mul_le_mul_of_nonneg_right ?_ htail0).trans
    (correctedLogarithmicQ_totalTail_le hn hk)
  unfold runwiseSamplerCalls
  push_cast
  exact_mod_cast Nat.mul_le_mul_right k (Nat.le_succ m)

/-- For cold variances (`sigmaSq ≤ 2`), the selected-radius mixing coefficient is
`O(n^3 + n log(A/b))`.  This is compatible with the capped radial-log source shape. -/
theorem hotCappedStepCoefficient_correctedLogarithmicQ_cold_le
    {n m k : Nat} (hn : 1 ≤ n) (hk : 0 < k)
    {sigmaSq : Real} (hsigma0 : 0 ≤ sigmaSq) (hsigma2 : sigmaSq ≤ 2) :
    hotCappedStepCoefficient n (correctedLogarithmicQ n m k) sigmaSq ≤
      (88 + 16 * Real.log (20 * runwiseSamplerCalls m k)) * (n : Real) ^ 3 := by
  have hA : 0 < runwiseSamplerCalls m k := by
    unfold runwiseSamplerCalls
    positivity
  have hbA : (1 / 20 : Real) ≤ runwiseSamplerCalls m k := by
    have hAone : (1 : Real) ≤ runwiseSamplerCalls m k := by
      unfold runwiseSamplerCalls
      norm_num
      exact_mod_cast Nat.mul_pos (Nat.succ_pos m) hk
    linarith
  have hq := max_eight_two_logarithmicAdaptiveRadiusQ_sq_le
    hn (by norm_num : (0 : Real) < 1 / 20) hbA
  have hlog0 : 0 ≤ Real.log (20 * runwiseSamplerCalls m k) := by
    apply Real.log_nonneg
    have hAone : (1 : Real) ≤ runwiseSamplerCalls m k := by
      unfold runwiseSamplerCalls
      norm_num
      exact_mod_cast Nat.mul_pos (Nat.succ_pos m) hk
    nlinarith
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : Real) ≤ n := by positivity
  have hq' : max 8 (2 * correctedLogarithmicQ n m k) ^ 2 ≤
      80 + 16 * Real.log (20 * runwiseSamplerCalls m k) / (n : Real) := by
    unfold correctedLogarithmicQ
    simpa only [show runwiseSamplerCalls m k / (1 / 20) =
        20 * runwiseSamplerCalls m k by ring] using hq
  have hsigmaTerm : 4 * sigmaSq * (n : Real) ^ 3 ≤
      8 * (n : Real) ^ 3 := by
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have hqTerm :
      max 8 (2 * correctedLogarithmicQ n m k) ^ 2 * (n : Real) ^ 2 ≤
        (80 + 16 * Real.log (20 * runwiseSamplerCalls m k)) *
          (n : Real) ^ 3 := by
    calc
      _ ≤ (80 + 16 * Real.log (20 * runwiseSamplerCalls m k) / (n : Real)) *
          (n : Real) ^ 2 := mul_le_mul_of_nonneg_right hq' (sq_nonneg _)
      _ = 80 * (n : Real) ^ 2 +
          16 * Real.log (20 * runwiseSamplerCalls m k) * (n : Real) := by
            field_simp
      _ ≤ 80 * (n : Real) ^ 3 +
          16 * Real.log (20 * runwiseSamplerCalls m k) * (n : Real) ^ 3 := by
            gcongr
            · nlinarith [mul_nonneg (sq_nonneg (n : Real))
                (sub_nonneg.mpr hnR)]
            · nlinarith [mul_nonneg hlog0
                (mul_nonneg hn0 (sub_nonneg.mpr
                  (show (1 : Real) ≤ (n : Real) ^ 2 by nlinarith)))]
      _ = (80 + 16 * Real.log (20 * runwiseSamplerCalls m k)) *
          (n : Real) ^ 3 := by ring
  unfold hotCappedStepCoefficient
  calc
    _ ≤ (80 + 16 * Real.log (20 * runwiseSamplerCalls m k)) *
          (n : Real) ^ 3 + 8 * (n : Real) ^ 3 := add_le_add hqTerm hsigmaTerm
    _ = (88 + 16 * Real.log (20 * runwiseSamplerCalls m k)) *
          (n : Real) ^ 3 := by ring

noncomputable def coldGlobalAdjustableDelta
    (n phaseCount streams : Nat) (sigmaSq : Real) : Real :=
  let q := correctedLogarithmicQ n phaseCount streams
  min (Real.sqrt sigmaSq / (max 8 (2 * q) * Real.sqrt n))
    (1 / (2 * (n : Real)))

noncomputable def coldGlobalRecursiveDeadlineEnvelope
    (n phaseCount streams L i : Nat) (initial : ENNReal) (share : Real) : Nat :=
  ⌈4 * 640 ^ 2 *
      ((88 + 16 * Real.log (20 * runwiseSamplerCalls phaseCount streams)) *
        (n : Real) ^ 3) *
      coldRecursiveWarmDeadlineLogEnvelope L i initial share /
        Real.log 2 ^ 2 + 1⌉₊ + 1

/-- Literal recursive-warm cold deadline with the one global, tail-fitting adjustable
radius.  The only new overhead compared with the fixed-radius cold coefficient is
`log(20 A)`, where `A` is the total number of calls. -/
theorem adjustableSpeedyDeadline_coldGlobalQ_recursiveWarm_scoreAware_le
    {n phaseCount streams cold scoreM scoreK L i : Nat}
    {s0 eps : Real} {slack boundSq : Nat → Real}
    {retries : Nat → Nat} {initial : ENNReal}
    (hn : 2 ≤ n) (hstreams : 0 < streams)
    (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hi : i < cold) (hcold : cold ≤ Ttc.CVHybridSchedule.coldPhases n s0)
    (hretries : ∀ j, retries j ≤ L)
    (hinitial : 1 ≤ initial) (hinitialTop : initial ≠ ⊤)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j) :
    adjustableSpeedyDeadline n
        (coldGlobalAdjustableDelta n phaseCount streams (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)
        ((2 * recursiveWarmBudget initial (coldAcceptedFactor n retries)
          (coldConcreteFallbackFactor n cold) i) /
            scoreAwareEta scoreM scoreK eps slack boundSq i)
        (scoreAwareZeta scoreM scoreK eps slack boundSq i) ≤
      coldGlobalRecursiveDeadlineEnvelope n phaseCount streams L i initial
        (scoreAwareShare scoreM scoreK eps slack boundSq i) := by
  apply adjustableSpeedyDeadline_le_ceil_of_expression_le
  let s := fixedSigmaSq n s0 i
  let q := correctedLogarithmicQ n phaseCount streams
  let d := coldGlobalAdjustableDelta n phaseCount streams s
  let payload := Real.log (((2 * recursiveWarmBudget initial
      (coldAcceptedFactor n retries) (coldConcreteFallbackFactor n cold) i) /
        scoreAwareEta scoreM scoreK eps slack boundSq i).toReal) +
      2 * Real.log (1 / (scoreAwareZeta scoreM scoreK eps slack boundSq i).toReal)
  let envelope := coldRecursiveWarmDeadlineLogEnvelope L i initial
    (scoreAwareShare scoreM scoreK eps slack boundSq i)
  let coefficient := (88 +
      16 * Real.log (20 * runwiseSamplerCalls phaseCount streams)) * (n : Real) ^ 3
  have hs : 0 < s := by
    dsimp only [s]
    unfold fixedSigmaSq
    exact Arlib.GaussianCooling.geomSchedule_pos hs0 (by positivity) i
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < q := by
    dsimp only [q]
    exact lt_trans (by norm_num)
      (correctedLogarithmicQ_tailFits (by omega : 1 ≤ n) hstreams).1
  have hd : 0 < d := by
    dsimp only [d, coldGlobalAdjustableDelta]
    exact lt_min
      (div_pos (Real.sqrt_pos.2 hs)
        (mul_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
          (Real.sqrt_pos.2 hnR)))
      (by positivity)
  have hpayload : payload ≤ envelope := by
    dsimp only [payload, envelope]
    exact coldRecursiveWarm_deadlineLogPayload_scoreAware_le
      (by omega : 1 ≤ n) (Nat.le_of_lt hi) hretries
        hinitial hinitialTop heps hslack hbound
  have henv0 : 0 ≤ envelope := by
    dsimp only [envelope]
    exact coldRecursiveWarmDeadlineLogEnvelope_nonneg
      hinitial hinitialTop heps heps1 hslack hbound
  have hsTwo : s ≤ 2 := by
    dsimp only [s]
    exact fixedSigmaSq_le_two_of_lt_coldPhases
      (by omega : 1 ≤ n) hs0 hs01 (lt_of_lt_of_le hi hcold)
  have hgeom0 : s * (n : Real) / d ^ 2 ≤ hotCappedStepCoefficient n q s := by
    dsimp only [d, coldGlobalAdjustableDelta, q]
    exact sigmaSq_mul_n_div_adaptiveTerminalDeltaQ_sq_le
      (by omega : 1 ≤ n) hs
  have hgeom1 : hotCappedStepCoefficient n q s ≤ coefficient := by
    dsimp only [q, coefficient]
    exact hotCappedStepCoefficient_correctedLogarithmicQ_cold_le
      (by omega : 1 ≤ n) hstreams hs.le hsTwo
  have hstep : (s * (n : Real) / d ^ 2) * payload ≤ coefficient * envelope := by
    calc
      _ ≤ (s * (n : Real) / d ^ 2) * envelope :=
        mul_le_mul_of_nonneg_left hpayload (by positivity)
      _ ≤ hotCappedStepCoefficient n q s * envelope :=
        mul_le_mul_of_nonneg_right hgeom0 henv0
      _ ≤ coefficient * envelope :=
        mul_le_mul_of_nonneg_right hgeom1 henv0
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep (by positivity : (0 : Real) ≤ 4 * 640 ^ 2))
    (sq_nonneg (Real.log 2))
  unfold adjustableSpeedyDeadlineExpression
  dsimp only [s, q, d, payload, envelope, coefficient] at hscaled
  have hleft :
      4 * 640 ^ 2 * fixedSigmaSq n s0 i * (n : Real) *
          (Real.log (((2 * recursiveWarmBudget initial
              (coldAcceptedFactor n retries)
              (coldConcreteFallbackFactor n cold) i) /
                scoreAwareEta scoreM scoreK eps slack boundSq i).toReal) +
            2 * Real.log (1 /
              (scoreAwareZeta scoreM scoreK eps slack boundSq i).toReal)) /
            (coldGlobalAdjustableDelta n phaseCount streams
              (fixedSigmaSq n s0 i) * Real.log 2) ^ 2 =
        (4 * 640 ^ 2 *
          ((fixedSigmaSq n s0 i * (n : Real) /
            coldGlobalAdjustableDelta n phaseCount streams
              (fixedSigmaSq n s0 i) ^ 2) *
            (Real.log (((2 * recursiveWarmBudget initial
                (coldAcceptedFactor n retries)
                (coldConcreteFallbackFactor n cold) i) /
                  scoreAwareEta scoreM scoreK eps slack boundSq i).toReal) +
              2 * Real.log (1 /
                (scoreAwareZeta scoreM scoreK eps slack boundSq i).toReal)))) /
          Real.log 2 ^ 2 := by
    field_simp [hd.ne', hlog.ne']
  rw [hleft]
  simpa only [add_comm, mul_assoc] using add_le_add_right hscaled 1

#print axioms correctedLogarithmicQ_totalTail_le
#print axioms activeCalls_correctedLogarithmicQ_totalTail_le
#print axioms hotCappedStepCoefficient_correctedLogarithmicQ_cold_le
#print axioms exists_activeCalls_radiusFour_tail_gt
#print axioms adjustableSpeedyDeadline_coldGlobalQ_recursiveWarm_scoreAware_le

end Ttc.CVGlobalAdjustableRadiusAudit
