import Ttc.Volume.CVCorrectedRuntime
import Ttc.Exec.CVIndependentStreamMoments

/-!
# Scalar arithmetic for corrected CV clipping

This file isolates the numerical facts needed when a scalar relative second-moment
factor `7` is averaged over the corrected number of independent streams and the
resulting empirical statistic is clipped.  The exact corrected parameters leave less
than two units between the real truncation level and the natural sample count; that
is enough for the factor `1 + 6/k` to absorb the clipping normalization and remain
below `1 + 8/k`.
-/

namespace Ttc.CVCorrectedClippingArithmetic

open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open MeasureTheory
open Ttc.CVIndependentStreamMoments

variable {Path : Type*} [MeasurableSpace Path]

/-- A scalar relative second-moment factor `7` becomes the empirical factor
`1 + 6/k` after averaging `k` independent complete streams. -/
theorem integral_streamAverage_sq_le_seven
    {k : Nat} (hk : 0 < k) (mu : Measure Path) [IsProbabilityMeasure mu]
    {g : Path → Real} (hg : Measurable g) (hL2 : MemLp g 2 mu)
    {mean : Real} (hmean : ∫ x, g x ∂mu = mean)
    (hsq : ∫ x, (g x) ^ 2 ∂mu ≤ 7 * mean ^ 2) :
    ∫ omega, (streamAverage (k := k) g omega) ^ 2
        ∂(independentStreamLaw mu) ≤
      (1 + 6 / (k : Real)) * mean ^ 2 := by
  simpa only [show (7 : Real) - 1 = 6 by norm_num] using
    integral_streamAverage_sq_le hk mu hg hL2 hmean hsq

/-- A generic form of the scalar clipping inequality.  It exposes exactly the two
ceil bounds used by the corrected runtime sample count. -/
theorem six_over_clipping_sq_le_eight_of_nearby
    {k alpha : Real} (halpha : 10 ≤ alpha) (halphaK : alpha ≤ k)
    (hkAlpha : k < alpha + 2) :
    (1 + 6 / k) / (1 - 1 / (2 * alpha)) ^ 2 ≤ 1 + 8 / k := by
  have ha0 : 0 < alpha := by linarith
  have hk0 : 0 < k := ha0.trans_le halphaK
  have hd0 : 0 < 1 - 1 / (2 * alpha) := by
    rw [sub_pos, div_lt_one (by positivity)]
    linarith
  rw [div_le_iff₀ (sq_pos_of_pos hd0)]
  field_simp [ne_of_gt hk0, ne_of_gt ha0]
  nlinarith

/-- The corrected truncation level is uniformly at least `100000` on the public
accuracy range. -/
theorem correctedAlpha_ge_hundred_thousand
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    100000 ≤ correctedAlpha m eps := by
  have hepsSq : eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg eps]
  have hm0 : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have hm : (1 : Real) ≤ (m : Real) + 1 := by linarith
  rw [correctedAlpha, le_div_iff₀ (sq_pos_of_pos heps)]
  nlinarith

/-- The real truncation level lies below the cast corrected sample count. -/
theorem correctedAlpha_le_runtimeSamples_cast
    {m : Nat} {eps : Real} :
    correctedAlpha m eps ≤ (correctedRuntimeSamples m eps : Real) := by
  have hceil := Nat.le_ceil (correctedAlpha m eps)
  calc
    correctedAlpha m eps ≤ (⌈correctedAlpha m eps⌉₊ : Real) := hceil
    _ ≤ ((⌈correctedAlpha m eps⌉₊ + 1 : Nat) : Real) := by
      exact_mod_cast Nat.le_succ _
    _ = (correctedRuntimeSamples m eps : Real) := by
      rw [correctedRuntimeSamples, correctedAlpha]

/-- The corrected sample count is strictly less than two above the real truncation
level. -/
theorem correctedRuntimeSamples_cast_lt_alpha_add_two
    {m : Nat} {eps : Real} (heps : 0 < eps) :
    (correctedRuntimeSamples m eps : Real) < correctedAlpha m eps + 2 := by
  simpa only [correctedAlpha] using
    (correctedRuntimeSamples_cast_lt (m := m) heps)

/-- In particular the corrected number of independent streams is at least eight. -/
theorem eight_le_correctedRuntimeSamples
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    8 ≤ correctedRuntimeSamples m eps := by
  have ha := correctedAlpha_ge_hundred_thousand (m := m) heps heps1
  have hak := correctedAlpha_le_runtimeSamples_cast (m := m) (eps := eps)
  exact_mod_cast (show (8 : Real) ≤ (correctedRuntimeSamples m eps : Real) by linarith)

/-- Exact scalar clipping inequality at the current corrected CV parameters. -/
theorem correctedRuntime_six_over_clipping_sq_le_eight
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (1 + 6 / (correctedRuntimeSamples m eps : Real)) /
        (1 - 1 / (2 * correctedAlpha m eps)) ^ 2 ≤
      1 + 8 / (correctedRuntimeSamples m eps : Real) := by
  apply six_over_clipping_sq_le_eight_of_nearby
  · exact (show (10 : Real) ≤ 100000 by norm_num).trans
      (correctedAlpha_ge_hundred_thousand (m := m) heps heps1)
  · exact correctedAlpha_le_runtimeSamples_cast
  · exact correctedRuntimeSamples_cast_lt_alpha_add_two heps

/-- Positivity of the clipping denominator at the current parameters. -/
theorem correctedRuntime_clippingDenominator_pos
    {m : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    0 < 1 - 1 / (2 * correctedAlpha m eps) := by
  have ha := correctedAlpha_ge_hundred_thousand (m := m) heps heps1
  rw [sub_pos, div_lt_one (by positivity)]
  linarith

#print axioms six_over_clipping_sq_le_eight_of_nearby
#print axioms integral_streamAverage_sq_le_seven
#print axioms correctedAlpha_ge_hundred_thousand
#print axioms correctedAlpha_le_runtimeSamples_cast
#print axioms correctedRuntimeSamples_cast_lt_alpha_add_two
#print axioms eight_le_correctedRuntimeSamples
#print axioms correctedRuntime_six_over_clipping_sq_le_eight
#print axioms correctedRuntime_clippingDenominator_pos

end Ttc.CVCorrectedClippingArithmetic
