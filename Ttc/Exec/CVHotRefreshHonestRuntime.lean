import Ttc.Exec.CVHotRefreshDeadline
import Ttc.Exec.CVRadialLogEnvelope
import Ttc.Volume.AdaptiveTerminalWarmLawAdjustable

/-!
# Honest step-size accounting for refreshed hot phases

The adjustable Gaussian kernel is required to use

`min (sqrt(s) / (max 8 (2*q) * sqrt n)) (1 / (2*n))`.

The second branch is operationally necessary for the rejection-cost theorem.  It
contributes `4*s*n^3` to the mixing coefficient and therefore cannot be discarded
from a source-runtime comparison.  This module records a branch-independent upper
bound used by the final refreshed-hot cost audit.
-/

set_option autoImplicit false

namespace Ttc.CVHotRefreshHonestRuntime

open Ttc.CVAdaptive
open Ttc.CVHotRefreshDeadline
open Ttc.CVHotRefreshRadialRuntime
open Ttc.CVRadialLogEnvelope
open Ttc.CVCorrectedRuntime
open Arlib.GaussianCooling.Chunked
open Arlib.GaussianCooling
open scoped ENNReal

/-- The two honest branches of `sigmaSq * n / delta^2`, with a sum replacing
the branch maximum. -/
noncomputable def hotCappedStepCoefficient
    (n : Nat) (q sigmaSq : Real) : Real :=
  (max 8 (2 * q)) ^ 2 * (n : Real) ^ 2 +
    4 * sigmaSq * (n : Real) ^ 3

/-- Dimension-aware replacement for the old `4*q^2` hot coefficient. -/
noncomputable def hotEffectiveQSq (n : Nat) (q : Real) : Real :=
  (max 8 (2 * q)) ^ 2 + 4 * (n : Real)

theorem hotCappedStepCoefficient_le_effective
    (n : Nat) (q : Real) {sigmaSq : Real} (hsigma : 1 ≤ sigmaSq) :
    hotCappedStepCoefficient n q sigmaSq ≤
      hotEffectiveQSq n q * sigmaSq * (n : Real) ^ 2 := by
  unfold hotCappedStepCoefficient hotEffectiveQSq
  have hn0 : (0 : Real) ≤ n := by positivity
  have hA0 : 0 ≤ (max 8 (2 * q)) ^ 2 := sq_nonneg _
  have hA : (max 8 (2 * q)) ^ 2 ≤
      (max 8 (2 * q)) ^ 2 * sigmaSq := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsigma hA0
  calc
    (max 8 (2 * q)) ^ 2 * (n : Real) ^ 2 +
        4 * sigmaSq * (n : Real) ^ 3 ≤
      (max 8 (2 * q)) ^ 2 * sigmaSq * (n : Real) ^ 2 +
        4 * sigmaSq * (n : Real) ^ 3 := by
          exact add_le_add (mul_le_mul_of_nonneg_right hA (sq_nonneg _)) le_rfl
    _ = ((max 8 (2 * q)) ^ 2 + 4 * (n : Real)) *
        sigmaSq * (n : Real) ^ 2 := by ring

/-- Sum of the honest capped-step coefficients over the source-hot coordinates. -/
noncomputable def adaptiveSourceHotCappedStepAccounting
    (n : Nat) (q N s0 : Real) (J : Nat) : Real :=
  ∑ j ∈ Finset.range J,
    ∑ t ∈ Finset.range (adaptiveChunkPhases N s0 j),
      if 1 < geomSchedule (adaptiveChunkStart N s0 j)
          (adaptiveChunkRate N s0 j) t then
        hotCappedStepCoefficient n q
          (geomSchedule (adaptiveChunkStart N s0 j)
            (adaptiveChunkRate N s0 j) t)
      else 0

/-- Before chunk cancellation, the corrected hot coefficient is exactly controlled by
the source hot variance mass with `hotEffectiveQSq`. -/
theorem adaptiveSourceHotCappedStepAccounting_le_mass
    (n : Nat) (q N s0 : Real) (J : Nat) :
    adaptiveSourceHotCappedStepAccounting n q N s0 J ≤
      hotEffectiveQSq n q * (n : Real) ^ 2 *
        adaptiveSourceHotSigmaMass N s0 J := by
  unfold adaptiveSourceHotCappedStepAccounting adaptiveSourceHotSigmaMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  split_ifs with hhot
  · simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (hotCappedStepCoefficient_le_effective n q hhot.le)
  · simp

/-- Honest chunk-cancelled hot accounting.  For `q ≥ 4`, the coefficient simplifies
to `24 * (q^2+n) * n^2 * N * J`; the unsimplified form also covers small `q`. -/
theorem adaptiveSourceHotCappedStepAccounting_le
    {n J : Nat} {q N s0 : Real} (hN : 0 < N) (hs0 : 0 < s0)
    (hbelow : ∀ j < J, adaptiveChunkStart N s0 j ≤ N) :
    adaptiveSourceHotCappedStepAccounting n q N s0 J ≤
      6 * hotEffectiveQSq n q * (n : Real) ^ 2 * N * J := by
  have hmass := adaptiveSourceHotSigmaMass_le hN hs0 hbelow
  have heff0 : 0 ≤ hotEffectiveQSq n q * (n : Real) ^ 2 := by
    unfold hotEffectiveQSq
    positivity
  calc
    adaptiveSourceHotCappedStepAccounting n q N s0 J ≤
        hotEffectiveQSq n q * (n : Real) ^ 2 *
          adaptiveSourceHotSigmaMass N s0 J :=
      adaptiveSourceHotCappedStepAccounting_le_mass n q N s0 J
    _ ≤ hotEffectiveQSq n q * (n : Real) ^ 2 * (6 * N * J) := by
      exact mul_le_mul_of_nonneg_left hmass heff0
    _ = 6 * hotEffectiveQSq n q * (n : Real) ^ 2 * N * J := by ring

theorem hotEffectiveQSq_eq_four_mul_add
    {n : Nat} {q : Real} (hq : 4 ≤ q) :
    hotEffectiveQSq n q = 4 * (q ^ 2 + (n : Real)) := by
  have hmax : max 8 (2 * q) = 2 * q := by
    rw [max_eq_right]
    linarith
  rw [hotEffectiveQSq, hmax]
  ring

/-- Honest one-run core after absorbing the capped hot step.  This is the old radial-log
core times one clipped dimension factor. -/
noncomputable def sourceCappedRadialLogOneRunQueryCore
    (runtimeConstant : Real) (n : Nat) (radius eps N : Real) : Real :=
  sourceRadialLogOneRunQueryCore runtimeConstant n radius eps N *
    max 1 (n : Real)

/-- Public complexity shape corresponding to
`sourceCappedRadialLogOneRunQueryCore`. -/
noncomputable def cvCappedRadialLogComplexityShapeClipped
    (n : Nat) (R2 eps p : Real) : Real :=
  cvRadialLogComplexityShapeClipped n R2 eps p * max 1 (n : Real)

theorem cvCappedRadialLogComplexityShapeClipped_nonneg
    (n : Nat) {R2 eps p : Real} (hR2 : 0 ≤ R2) :
    0 ≤ cvCappedRadialLogComplexityShapeClipped n R2 eps p := by
  unfold cvCappedRadialLogComplexityShapeClipped
  exact mul_nonneg
    (cvRadialLogComplexityShapeClipped_nonneg n R2 eps p hR2)
    (zero_le_one.trans (le_max_left _ _))

theorem cvRadialLogComplexityShapeClipped_le_capped
    (n : Nat) {R2 eps p : Real} (hR2 : 0 ≤ R2) :
    cvRadialLogComplexityShapeClipped n R2 eps p ≤
      cvCappedRadialLogComplexityShapeClipped n R2 eps p := by
  unfold cvCappedRadialLogComplexityShapeClipped
  exact le_mul_of_one_le_right
    (cvRadialLogComplexityShapeClipped_nonneg n R2 eps p hR2)
    (le_max_left _ _)

theorem sourceRadialLogOneRunQueryCore_le_capped
    {runtimeConstant : Real} (hconstant : 0 ≤ runtimeConstant)
    (n : Nat) (radius eps N : Real) :
    sourceRadialLogOneRunQueryCore runtimeConstant n radius eps N ≤
      sourceCappedRadialLogOneRunQueryCore runtimeConstant n radius eps N := by
  unfold sourceCappedRadialLogOneRunQueryCore
  have hcore : 0 ≤ sourceRadialLogOneRunQueryCore
      runtimeConstant n radius eps N := by
    unfold sourceRadialLogOneRunQueryCore
      Ttc.CVColdHotReferenceCost.sourceOneRunQueryCore
    positivity
  exact le_mul_of_one_le_right hcore (le_max_left _ _)

theorem hotCappedStepCoefficient_nonneg
    (n : Nat) (q sigmaSq : Real) (hsigma : 0 ≤ sigmaSq) :
    0 ≤ hotCappedStepCoefficient n q sigmaSq := by
  unfold hotCappedStepCoefficient
  positivity

/-- Exact branch-safe estimate for the coefficient occurring in the adjustable
mixing deadline. -/
theorem sigmaSq_mul_n_div_adaptiveTerminalDeltaQ_sq_le
    {n : Nat} (hn : 1 ≤ n) {q sigmaSq : Real}
    (hsigma : 0 < sigmaSq) :
    sigmaSq * (n : Real) /
        (min (Real.sqrt sigmaSq /
            (max 8 (2 * q) * Real.sqrt n))
          (1 / (2 * (n : Real)))) ^ 2 ≤
      hotCappedStepCoefficient n q sigmaSq := by
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hsqrtN : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hA : 0 < max 8 (2 * q) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hsqrtS : 0 < Real.sqrt sigmaSq := Real.sqrt_pos.2 hsigma
  let a := Real.sqrt sigmaSq / (max 8 (2 * q) * Real.sqrt n)
  let b := 1 / (2 * (n : Real))
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  by_cases hab : a ≤ b
  · rw [min_eq_left hab]
    have hsqrtSq : (Real.sqrt sigmaSq) ^ 2 = sigmaSq :=
      Real.sq_sqrt hsigma.le
    have hsqrtNSq : (Real.sqrt (n : Real)) ^ 2 = (n : Real) :=
      Real.sq_sqrt hnR.le
    have hcalc : sigmaSq * (n : Real) / a ^ 2 =
        (max 8 (2 * q)) ^ 2 * (n : Real) ^ 2 := by
      dsimp only [a]
      field_simp [hsqrtS.ne', hsqrtN.ne', hA.ne']
      nlinarith [hsqrtNSq]
    rw [hcalc]
    unfold hotCappedStepCoefficient
    exact le_add_of_nonneg_right (by positivity)
  · rw [min_eq_right (le_of_not_ge hab)]
    have hcalc : sigmaSq * (n : Real) / b ^ 2 =
        4 * sigmaSq * (n : Real) ^ 3 := by
      dsimp only [b]
      field_simp [hnR.ne']
      ring
    rw [hcalc]
    unfold hotCappedStepCoefficient
    exact le_add_of_nonneg_left (by positivity)

/-- Specialization to the literal adaptive hot step. -/
theorem sigmaSq_mul_n_div_adaptiveTerminalDeltaQ_sq_le_coefficient
    {n : Nat} (hn : 1 ≤ n) {q N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (i : Nat) :
    adaptiveSigmaSq N s0 i * (n : Real) /
        (adaptiveTerminalDeltaQ (n := n) q N s0 i) ^ 2 ≤
      hotCappedStepCoefficient n q (adaptiveSigmaSq N s0 i) := by
  unfold adaptiveTerminalDeltaQ adaptiveTerminalSigma
  exact sigmaSq_mul_n_div_adaptiveTerminalDeltaQ_sq_le hn
    (adaptiveSigmaSq_pos hN hs0 i)

/-- The capped branch genuinely has one more factor of dimension than the old
`q^2*n^2*sigmaSq` charge.  This exact identity is useful when auditing any
claimed source-shaped hot bound. -/
theorem sigmaSq_mul_n_div_cap_sq
    {n : Nat} (hn : 1 ≤ n) (sigmaSq : Real) :
    sigmaSq * (n : Real) / (1 / (2 * (n : Real))) ^ 2 =
      4 * sigmaSq * (n : Real) ^ 3 := by
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  field_simp [hnR.ne']
  ring

#print axioms sigmaSq_mul_n_div_adaptiveTerminalDeltaQ_sq_le
#print axioms sigmaSq_mul_n_div_adaptiveTerminalDeltaQ_sq_le_coefficient
#print axioms sigmaSq_mul_n_div_cap_sq
#print axioms sourceRadialLogOneRunQueryCore_le_capped
#print axioms adaptiveSourceHotCappedStepAccounting_le
#print axioms cvRadialLogComplexityShapeClipped_le_capped

end Ttc.CVHotRefreshHonestRuntime
