import Ttc.Exec.CVIndependentRefreshSeedLaws
import Ttc.Volume.CVMomentAdjustableAccuracy
import Ttc.Volume.CVHybridSchedule
import Ttc.Exec.CVSourcePolynomialCutoffCapstone

/-!
# Radial runtime bounds for independent hot-phase refreshes

This file connects the fixed-ball refresh law to the actual public moment-truncated body
and the two-regime hybrid schedule.  It deliberately contains no certificate assembly:
the results are small reusable inputs for the operational and hybrid capstones.
-/

set_option autoImplicit false

namespace Ttc.CVHotRefreshRadialRuntime

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVAdaptive Ttc.CVHybridSchedule
open Ttc.CVIndependentRefreshSeedLaws
open Ttc.CVSourcePolynomialCutoffCapstone
open scoped BigOperators

variable {n : Nat}

/-- Polynomial square-radius envelope supplied by Markov moment truncation. -/
noncomputable def momentRefreshRadiusSqEnvelope
    (n : Nat) (R2 eta : Real) : Real :=
  2 * (n : Real) + 2 * R2 / eta

/-- Uniform hot-phase logarithmic core for the public moment body. -/
noncomputable def hotRefreshMomentLogCore
    (n : Nat) (R2 eta : Real) : Real :=
  1 / 32 + (n : Real) *
    Real.log (4 * max 1 (momentRefreshRadiusSqEnvelope n R2 eta))

/-- The adaptive tail of the hybrid schedule never falls below its starting variance. -/
theorem coldEnd_le_sigmaSq_of_not_lt_coldPhases
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    {i : Nat} (hi : ¬ i < coldPhases n s0) :
    coldEnd n s0 ≤ sigmaSq n N s0 i := by
  let t : Nat := i - coldPhases n s0
  let j : Nat := adaptivePhaseChunk N (coldEnd n s0) t
  have hend0 : 0 < coldEnd n s0 := coldEnd_pos hn hs0
  have hpow : (1 : Real) ≤ (2 : Real) ^ j := one_le_pow₀ (by norm_num)
  have hstart : coldEnd n s0 ≤ adaptiveChunkStart N (coldEnd n s0) j := by
    calc
      coldEnd n s0 = 1 * coldEnd n s0 := by ring
      _ ≤ (2 : Real) ^ j * coldEnd n s0 := by
        exact mul_le_mul_of_nonneg_right hpow hend0.le
      _ ≤ adaptiveChunkStart N (coldEnd n s0) j :=
        pow_two_mul_le_adaptiveChunkStart hN hend0 j
  have hphase : adaptiveChunkStart N (coldEnd n s0) j ≤
      adaptiveSigmaSq N (coldEnd n s0) t := by
    exact adaptiveChunkStart_le_geom hN hend0 j
      (adaptiveLocalPhase N (coldEnd n s0) t)
  rw [sigmaSq, if_neg hi]
  exact hstart.trans hphase

/-- Every hot phase has variance at least one. -/
theorem one_le_sigmaSq_of_not_lt_coldPhases
    (hn : 1 ≤ n) {N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hs01 : s0 ≤ 1) {i : Nat} (hi : ¬ i < coldPhases n s0) :
    1 ≤ sigmaSq n N s0 i :=
  (one_le_coldEnd hn hs0 hs01).trans
    (coldEnd_le_sigmaSq_of_not_lt_coldPhases hn hN hs0 hi)

/-- The public moment-runtime body lies in the exact radial ball used in the refresh
normalizer estimate. -/
theorem momentRuntimeBody_subset_runtimeBall
    (K : Set (Ttc.Space n)) (R2 eta : Real) :
    momentRuntimeBody n K R2 eta ⊆
      closedBall 0 (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n) :=
  inter_subset_right

/-- Instantiation of the hot refresh ratio bound on the public moment-runtime body. -/
theorem hotRefreshWarmFactor_momentRuntimeBody_le_envelope
    {K : Set (Ttc.Space n)} {R2 eta s : Real} (hs : 0 < s) :
    gaussianBallWarmFactor (momentRuntimeBody n K R2 eta) s hotRefreshRadius ≤
      hotRefreshWarmEnvelope n
        (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n) s := by
  apply hotRefreshWarmFactor_le_envelope
    (isClosed_momentRuntimeBody (n := n) (K := K) (R2 := R2) (eta := eta)).measurableSet hs
  exact momentRuntimeBody_subset_runtimeBall K R2 eta

/-- The enclosing radius itself is controlled by the same polynomial that bounds its
square.  The `max 1` formulation is exactly what the logarithmic refresh envelope uses. -/
theorem max_one_momentRuntimeRadius_le_sqEnvelope
    (hn : 1 ≤ n) {R2 eta : Real} (hR2 : 0 < R2) (heta : 0 < eta) :
    max 1 (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n) ≤
      max 1 (momentRefreshRadiusSqEnvelope n R2 eta) := by
  let R : Real := markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n
  let B : Real := momentRefreshRadiusSqEnvelope n R2 eta
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg (markovRuntimeC_pos n (Real.sqrt R2) eta).le
      (Real.sqrt_nonneg _)
  have hR2B : R ^ 2 ≤ B := by
    have hsqrt : Real.sqrt (n : Real) ^ 2 = (n : Real) :=
      Real.sq_sqrt hn0.le
    have h := cvAdmissible_markovRuntimeC_sq_mul_n_le
      hn hR2 heta
    dsimp only [R, B, momentRefreshRadiusSqEnvelope]
    rw [mul_pow, hsqrt]
    exact h
  have hRB : R ≤ max 1 B := by
    by_cases hR1 : R ≤ 1
    · exact hR1.trans (le_max_left 1 B)
    · have h1R : 1 < R := lt_of_not_ge hR1
      have hRR2 : R ≤ R ^ 2 := by nlinarith
      exact (hRR2.trans hR2B).trans (le_max_right 1 B)
  exact max_le (le_max_left 1 B) hRB

/-- Radial logarithm of the runtime ball is bounded by a logarithm of the explicit
moment polynomial `2n + 2R2/eta`. -/
theorem log_momentRuntimeRadius_le_log_sqEnvelope
    (hn : 1 ≤ n) {R2 eta : Real} (hR2 : 0 < R2) (heta : 0 < eta) :
    Real.log
        (4 * max 1 (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n)) ≤
      Real.log (4 * max 1 (momentRefreshRadiusSqEnvelope n R2 eta)) := by
  have hpos : 0 <
      4 * max 1 (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n) := by
    have : (0 : Real) <
        max 1 (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n) :=
      one_pos.trans_le (le_max_left _ _)
    positivity
  apply Real.log_le_log hpos
  exact mul_le_mul_of_nonneg_left
    (max_one_momentRuntimeRadius_le_sqEnvelope hn hR2 heta) (by norm_num)

/-- The logarithm of the moment-body refresh envelope has the required radial form at
every hot phase. -/
theorem log_hotRefreshWarmEnvelope_momentRuntimeBody_hot_le
    (hn : 1 ≤ n) {N s0 R2 eta : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hs01 : s0 ≤ 1) {i : Nat} (hi : ¬ i < coldPhases n s0) :
    Real.log
        (hotRefreshWarmEnvelope n
          (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n)
          (sigmaSq n N s0 i)).toReal ≤
      1 / 32 + (n : Real) * Real.log
        (4 * max 1 (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n)) := by
  exact log_hotRefreshWarmEnvelope_toReal_le_of_one_le n
    (one_le_sigmaSq_of_not_lt_coldPhases hn hN hs0 hs01 hi)

/-- Final hot-phase refresh logarithm in the public moment-polynomial parameters. -/
theorem log_hotRefreshWarmEnvelope_momentPolynomial_hot_le
    (hn : 1 ≤ n) {N s0 R2 eta : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hs01 : s0 ≤ 1) (hR2 : 0 < R2) (heta : 0 < eta)
    {i : Nat} (hi : ¬ i < coldPhases n s0) :
    Real.log
        (hotRefreshWarmEnvelope n
          (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n)
          (sigmaSq n N s0 i)).toReal ≤
      1 / 32 + (n : Real) *
        Real.log (4 * max 1 (momentRefreshRadiusSqEnvelope n R2 eta)) := by
  have hraw := log_hotRefreshWarmEnvelope_momentRuntimeBody_hot_le
    hn hN hs0 hs01 hi (R2 := R2) (eta := eta)
  have hlog := log_momentRuntimeRadius_le_log_sqEnvelope hn hR2 heta
  have hn0 : (0 : Real) ≤ n := by positivity
  linarith [mul_le_mul_of_nonneg_left hlog hn0]

/-- The new refresh logarithm is absorbed by one dimension factor and one existing
clipped radial logarithm. -/
theorem hotRefreshMomentLogCore_le_five_mul_sourceLog
    (hn : 1 ≤ n) {R2 eta : Real} (hR2 : 0 < R2) (heta : 0 < eta) :
    hotRefreshMomentLogCore n R2 eta ≤
      5 * (n : Real) * sourceLogFactor
        (momentRefreshRadiusSqEnvelope n R2 eta) := by
  let B := momentRefreshRadiusSqEnvelope n R2 eta
  let L := sourceLogFactor B
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hB : 1 ≤ B := by
    dsimp only [B, momentRefreshRadiusSqEnvelope]
    have : (0 : Real) < 2 * R2 / eta := by positivity
    nlinarith
  have hL1 : 1 ≤ L := by
    dsimp only [L, sourceLogFactor]
    exact le_max_left _ _
  have hlogB : Real.log (max 1 B) ≤ L := by
    rw [max_eq_right hB]
    exact le_max_right _ _
  have hlog4 : Real.log (4 : Real) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (x := (4 : Real)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hlogMul : Real.log (4 * max 1 B) ≤ 3 + L := by
    rw [Real.log_mul (by norm_num : (4 : Real) ≠ 0)
      (ne_of_gt (one_pos.trans_le (le_max_left 1 B)))]
    linarith
  unfold hotRefreshMomentLogCore
  dsimp only [B, L] at hlogMul hL1 ⊢
  have hn0 : (0 : Real) ≤ n := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlogMul hn0
  have hnL : 1 ≤ (n : Real) * sourceLogFactor
      (momentRefreshRadiusSqEnvelope n R2 eta) := by
    nlinarith [mul_le_mul hnR hL1 (by norm_num : (0 : Real) ≤ 1) hn0]
  nlinarith

/-- Sum of all independent-refresh warm logarithms over an arbitrary prefix of the hot
block.  There is no compounding and hence no quadratic phase-count loss. -/
theorem sum_hotRefreshWarmLogs_le
    (hn : 1 ≤ n) {N s0 R2 eta : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hs01 : s0 ≤ 1) (hR2 : 0 < R2) (heta : 0 < eta) (hot : Nat) :
    (∑ q ∈ Finset.range hot,
      Real.log
        (hotRefreshWarmEnvelope n
          (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n)
          (sigmaSq n N s0 (coldPhases n s0 + q))).toReal) ≤
      (hot : Real) * hotRefreshMomentLogCore n R2 eta := by
  calc
    _ ≤ ∑ _q ∈ Finset.range hot, hotRefreshMomentLogCore n R2 eta := by
      apply Finset.sum_le_sum
      intro q hq
      exact log_hotRefreshWarmEnvelope_momentPolynomial_hot_le
        hn hN hs0 hs01 hR2 heta (by omega)
    _ = (hot : Real) * hotRefreshMomentLogCore n R2 eta := by simp

/-- Fully clipped radial-log form of the summed hot refresh overhead. -/
theorem sum_hotRefreshWarmLogs_le_sourceLog
    (hn : 1 ≤ n) {N s0 R2 eta : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hs01 : s0 ≤ 1) (hR2 : 0 < R2) (heta : 0 < eta) (hot : Nat) :
    (∑ q ∈ Finset.range hot,
      Real.log
        (hotRefreshWarmEnvelope n
          (markovRuntimeC n (Real.sqrt R2) eta * Real.sqrt n)
          (sigmaSq n N s0 (coldPhases n s0 + q))).toReal) ≤
      5 * (hot : Real) * (n : Real) * sourceLogFactor
        (momentRefreshRadiusSqEnvelope n R2 eta) := by
  have hsum := sum_hotRefreshWarmLogs_le hn hN hs0 hs01 hR2 heta hot
  have hcore := hotRefreshMomentLogCore_le_five_mul_sourceLog hn hR2 heta
  have hhot0 : (0 : Real) ≤ hot := by positivity
  calc
    _ ≤ (hot : Real) * hotRefreshMomentLogCore n R2 eta := hsum
    _ ≤ (hot : Real) *
        (5 * (n : Real) * sourceLogFactor
          (momentRefreshRadiusSqEnvelope n R2 eta)) :=
      mul_le_mul_of_nonneg_left hcore hhot0
    _ = _ := by ring

#print axioms coldEnd_le_sigmaSq_of_not_lt_coldPhases
#print axioms one_le_sigmaSq_of_not_lt_coldPhases
#print axioms hotRefreshWarmFactor_momentRuntimeBody_le_envelope
#print axioms log_hotRefreshWarmEnvelope_momentRuntimeBody_hot_le
#print axioms max_one_momentRuntimeRadius_le_sqEnvelope
#print axioms log_momentRuntimeRadius_le_log_sqEnvelope
#print axioms log_hotRefreshWarmEnvelope_momentPolynomial_hot_le
#print axioms hotRefreshMomentLogCore_le_five_mul_sourceLog
#print axioms sum_hotRefreshWarmLogs_le
#print axioms sum_hotRefreshWarmLogs_le_sourceLog

end Ttc.CVHotRefreshRadialRuntime
