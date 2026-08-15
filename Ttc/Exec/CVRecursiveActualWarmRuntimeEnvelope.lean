import Ttc.Exec.CVGlobalLogarithmicRadius
import Ttc.Exec.CVColdActualWarmReferenceCostArithmetic

/-!
# Closed cold-runtime envelope for the recursive actual-warm schedule

The recursive warm budget is not charged as a multiplicative expected-cost factor.
It is used only to select a mixing deadline, and hence contributes through its
logarithm.  This file combines the affine logarithmic bound from
`CVColdActualWarmReferenceCostArithmetic` with the run-global logarithmic truncation
radius.

The one schedule-specific scalar left visible is `shareLog`: a common upper bound on
`log (1 / scoreAwareShare i)`.  This is exactly the information about the chosen
second-moment slack needed to turn the result into a source-parameter-only bound.
-/

set_option autoImplicit false

namespace Ttc.CVRecursiveActualWarmRuntimeEnvelope

open Ttc.CVGlobalLogarithmicRadius
open Ttc.CVColdActualWarmReferenceCostArithmetic
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianScoreAwareSharpScheduleBound
open Ttc.CVGaussianAdaptiveMixing
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVHybridSchedule
open Ttc.CVWarmBudgetRecurrence
open Ttc.CVGaussianColdHotRecursiveStep
open scoped ENNReal BigOperators

/-- The exact residual share premise needed by the recursive cold accounting. -/
def RecursiveColdShareLogBound
    (m k cold : Nat) (eps : Real) (slack boundSq : Nat → Real)
    (shareLog : Real) : Prop :=
  ∀ i, i < cold →
    Real.log (1 / scoreAwareShare m k eps slack boundSq i) ≤ shareLog

/-- A uniform positive lower bound on the selected shares discharges the residual
share-log premise. -/
theorem recursiveColdShareLogBound_of_floor
    {m k cold : Nat} {eps floor : Real} {slack boundSq : Nat → Real}
    (hfloor0 : 0 < floor)
    (heps : 0 < eps) (hslack : ∀ i, 0 < slack i)
    (hbound : ∀ i, 0 < boundSq i)
    (hfloor : ∀ i, i < cold →
      floor ≤ scoreAwareShare m k eps slack boundSq i) :
    RecursiveColdShareLogBound m k cold eps slack boundSq
      (Real.log (1 / floor)) := by
  intro i hi
  have hshare0 := scoreAwareShare_pos (m := m) (k := k)
    heps hslack hbound i
  exact Real.log_le_log (one_div_pos.mpr hshare0)
    (one_div_le_one_div_of_le hfloor0 (hfloor i hi))

/-- A phase-uniform logarithmic envelope for the whole recursive cold prefix. -/
noncomputable def recursiveColdLogCap
    (L cold : Nat) (initial : ENNReal) (shareLog : Real) : Real :=
  Real.log initial.toReal +
    (cold : Real) * Real.log (coldLinearWarmBase L).toReal +
      Real.log 2 + 2 * Real.log 32 + 3 * shareLog

theorem coldRecursiveWarmDeadlineLogEnvelope_le_cap
    {m k L cold i : Nat} {eps shareLog : Real}
    {slack boundSq : Nat → Real} {initial : ENNReal}
    (hi : i < cold)
    (hshare : RecursiveColdShareLogBound m k cold eps slack boundSq shareLog) :
    coldRecursiveWarmDeadlineLogEnvelope L i initial
        (scoreAwareShare m k eps slack boundSq i) ≤
      recursiveColdLogCap L cold initial shareLog := by
  unfold coldRecursiveWarmDeadlineLogEnvelope recursiveColdLogCap
  have hlogBase : 0 ≤ Real.log (coldLinearWarmBase L).toReal := by
    apply Real.log_nonneg
    have htop : coldLinearWarmBase L ≠ ⊤ := by
      unfold coldLinearWarmBase
      exact ENNReal.add_ne_top.2
        ⟨max_ne_top (by norm_num)
          (ENNReal.mul_ne_top (ENNReal.natCast_ne_top L) (by norm_num)), by norm_num⟩
    have hone : (1 : ENNReal) ≤ coldLinearWarmBase L :=
      (by norm_num : (1 : ENNReal) ≤ 6).trans (six_le_coldLinearWarmBase L)
    simpa using ENNReal.toReal_mono htop hone
  have hicast : (i : Real) ≤ cold := by exact_mod_cast Nat.le_of_lt hi
  have hphase := mul_le_mul_of_nonneg_right hicast hlogBase
  have hs := hshare i hi
  linarith

/-- The sum of all cold logarithmic payloads has only one extra cold-prefix factor. -/
theorem sum_coldRecursiveWarmDeadlineLogEnvelope_le
    {m k L cold : Nat} {eps shareLog : Real}
    {slack boundSq : Nat → Real} {initial : ENNReal}
    (hshare : RecursiveColdShareLogBound m k cold eps slack boundSq shareLog) :
    ∑ i ∈ Finset.range cold,
        coldRecursiveWarmDeadlineLogEnvelope L i initial
          (scoreAwareShare m k eps slack boundSq i) ≤
      (cold : Real) * recursiveColdLogCap L cold initial shareLog := by
  calc
    _ ≤ ∑ _i ∈ Finset.range cold,
        recursiveColdLogCap L cold initial shareLog := by
      apply Finset.sum_le_sum
      intro i hi
      exact coldRecursiveWarmDeadlineLogEnvelope_le_cap
        (Finset.mem_range.mp hi) hshare
    _ = (cold : Real) * recursiveColdLogCap L cold initial shareLog := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Real expression whose ceiling bounds every cold deadline when the same global
logarithmic radius is used for all sampler calls. -/
noncomputable def recursiveGlobalColdDeadlineRealEnvelope
    (n : Nat) (A : Real) (L cold : Nat) (initial : ENNReal)
    (shareLog : Real) : Real :=
  4 * 640 ^ 2 *
      ((72 + 16 * Real.log (20 * A)) * (n : Real) ^ 3) *
      recursiveColdLogCap L cold initial shareLog / Real.log 2 ^ 2 + 1

noncomputable def recursiveGlobalColdDeadlineEnvelope
    (n : Nat) (A : Real) (L cold : Nat) (initial : ENNReal)
    (shareLog : Real) : Nat :=
  ⌈recursiveGlobalColdDeadlineRealEnvelope n A L cold initial shareLog⌉₊ + 1

/-- Literal phase deadline bound using both the recursive actual-warm budget and the
run-global logarithmic truncation radius. -/
theorem adjustableSpeedyDeadline_globalRadius_recursiveWarm_le
    {n cold m k L i : Nat} {A s0 eps shareLog : Real}
    {slack boundSq : Nat → Real} {retries : Nat → Nat}
    {initial : ENNReal}
    (hn : 2 ≤ n) (hA : 1 ≤ A) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hi : i < cold) (hcold : cold ≤ coldPhases n s0)
    (hretries : ∀ j, retries j ≤ L)
    (hinitial : 1 ≤ initial) (hinitialTop : initial ≠ ⊤)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j)
    (hshare : RecursiveColdShareLogBound m k cold eps slack boundSq shareLog) :
    adjustableSpeedyDeadline n
        (globalLogarithmicDelta n A (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)
        ((2 * recursiveWarmBudget initial (coldAcceptedFactor n retries)
          (coldConcreteFallbackFactor n cold) i) /
            scoreAwareEta m k eps slack boundSq i)
        (scoreAwareZeta m k eps slack boundSq i) ≤
      recursiveGlobalColdDeadlineEnvelope n A L cold initial shareLog := by
  apply adjustableSpeedyDeadline_le_ceil_of_expression_le
  let s := fixedSigmaSq n s0 i
  let d := globalLogarithmicDelta n A s
  let payload := Real.log (((2 * recursiveWarmBudget initial
      (coldAcceptedFactor n retries) (coldConcreteFallbackFactor n cold) i) /
        scoreAwareEta m k eps slack boundSq i).toReal) +
      2 * Real.log (1 / (scoreAwareZeta m k eps slack boundSq i).toReal)
  let cap := recursiveColdLogCap L cold initial shareLog
  have hs : 0 < s := by
    dsimp only [s]
    unfold fixedSigmaSq
    exact Arlib.GaussianCooling.geomSchedule_pos hs0 (by positivity) i
  have hs2 : s ≤ 2 := by
    dsimp only [s]
    exact fixedSigmaSq_le_two_of_lt_coldPhases (by omega) hs0 hs01
      (lt_of_lt_of_le hi hcold)
  have hd : 0 < d := by
    dsimp only [d]
    exact globalLogarithmicDelta_pos (by omega) hA hs
  have hpayload : payload ≤ cap := by
    have hraw := coldRecursiveWarm_deadlineLogPayload_scoreAware_le
      (n := n) (cold := cold) (m := m) (k := k) (L := L) (i := i)
      (eps := eps) (slack := slack) (boundSq := boundSq) (retries := retries)
      (initial := initial) (by omega) (Nat.le_of_lt hi) hretries
      hinitial hinitialTop heps hslack hbound
    simpa only [payload, cap] using
      hraw.trans (coldRecursiveWarmDeadlineLogEnvelope_le_cap hi hshare)
  have hcap0 : 0 ≤ cap := by
    have henv0 := coldRecursiveWarmDeadlineLogEnvelope_nonneg
      (m := m) (k := k) (L := L) (i := i) hinitial hinitialTop
        heps heps1 hslack hbound
    exact henv0.trans
      (coldRecursiveWarmDeadlineLogEnvelope_le_cap hi hshare)
  have hgeom : s * (n : Real) / d ^ 2 ≤
      (72 + 16 * Real.log (20 * A)) * (n : Real) ^ 3 := by
    dsimp only [s, d]
    exact sigmaSq_mul_n_div_globalDelta_sq_cold_le (by omega) hA hs hs2
  have hstep : (s * (n : Real) / d ^ 2) * payload ≤
      ((72 + 16 * Real.log (20 * A)) * (n : Real) ^ 3) * cap := by
    calc
      _ ≤ (s * (n : Real) / d ^ 2) * cap :=
        mul_le_mul_of_nonneg_left hpayload (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hgeom hcap0
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep (by positivity : (0 : Real) ≤ 4 * 640 ^ 2))
    (sq_nonneg (Real.log 2))
  unfold adjustableSpeedyDeadlineExpression
  dsimp only [s, d, payload, cap] at hscaled
  unfold recursiveGlobalColdDeadlineRealEnvelope
  have hleft :
      4 * 640 ^ 2 * fixedSigmaSq n s0 i * (n : Real) *
          (Real.log (((2 * recursiveWarmBudget initial
              (coldAcceptedFactor n retries) (coldConcreteFallbackFactor n cold) i) /
                scoreAwareEta m k eps slack boundSq i).toReal) +
            2 * Real.log (1 /
              (scoreAwareZeta m k eps slack boundSq i).toReal)) /
            (globalLogarithmicDelta n A (fixedSigmaSq n s0 i) * Real.log 2) ^ 2 =
        (4 * 640 ^ 2 *
          ((fixedSigmaSq n s0 i * (n : Real) /
            globalLogarithmicDelta n A (fixedSigmaSq n s0 i) ^ 2) *
            (Real.log (((2 * recursiveWarmBudget initial
                (coldAcceptedFactor n retries) (coldConcreteFallbackFactor n cold) i) /
                  scoreAwareEta m k eps slack boundSq i).toReal) +
              2 * Real.log (1 /
                (scoreAwareZeta m k eps slack boundSq i).toReal)))) /
          Real.log 2 ^ 2 := by
    field_simp [hd.ne', hlog.ne']
  rw [hleft]
  simpa only [add_comm, mul_assoc] using add_le_add_right hscaled 1

/-- Closed natural-number cost for all cold retries.  The only non-source parameter is
the explicitly displayed share-log cap. -/
theorem sum_retries_mul_globalRadius_recursiveWarm_le
    {n cold m k L : Nat} {A s0 eps shareLog : Real}
    {slack boundSq : Nat → Real} {retries : Nat → Nat}
    {initial : ENNReal}
    (hn : 2 ≤ n) (hA : 1 ≤ A) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (hcold : cold ≤ coldPhases n s0)
    (hretries : ∀ j, retries j ≤ L)
    (hinitial : 1 ≤ initial) (hinitialTop : initial ≠ ⊤)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ j, 0 < slack j) (hbound : ∀ j, 0 < boundSq j)
    (hshare : RecursiveColdShareLogBound m k cold eps slack boundSq shareLog) :
    ∑ i ∈ Finset.range cold,
        retries i * adjustableSpeedyDeadline n
          (globalLogarithmicDelta n A (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i)
          ((2 * recursiveWarmBudget initial (coldAcceptedFactor n retries)
            (coldConcreteFallbackFactor n cold) i) /
              scoreAwareEta m k eps slack boundSq i)
          (scoreAwareZeta m k eps slack boundSq i) ≤
      cold * (L * recursiveGlobalColdDeadlineEnvelope
        n A L cold initial shareLog) := by
  calc
    _ ≤ ∑ _i ∈ Finset.range cold,
        L * recursiveGlobalColdDeadlineEnvelope n A L cold initial shareLog := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul (hretries i)
        (adjustableSpeedyDeadline_globalRadius_recursiveWarm_le
          hn hA hs0 hs01 (Finset.mem_range.mp hi) hcold hretries
          hinitial hinitialTop heps heps1 hslack hbound hshare)
    _ = cold * (L * recursiveGlobalColdDeadlineEnvelope
        n A L cold initial shareLog) := by simp

#print axioms sum_coldRecursiveWarmDeadlineLogEnvelope_le
#print axioms adjustableSpeedyDeadline_globalRadius_recursiveWarm_le
#print axioms sum_retries_mul_globalRadius_recursiveWarm_le

end Ttc.CVRecursiveActualWarmRuntimeEnvelope
