import Ttc.Exec.CVAdaptiveRadiusQCrossWarm

/-! Constant warmth of adjustable-radius transitions under source-small rates. -/

set_option autoImplicit false

namespace Ttc.CVAdaptiveRadiusQSmallRateWarm

open Arlib Arlib.GaussianCooling Arlib.GaussianCooling.Chunked
open Ttc.CVAdaptiveRadiusQCrossWarm
open scoped ENNReal

/-- If the truncated-body variance rate remains at most `1/n`, changing the radius
costs only the universal factor `2e`, rather than an exponential-in-dimension factor. -/
theorem adaptiveRadiusQWarmFactor_one_add_le_two_exp
    {n : Nat} (hn : 1 ≤ n) {r : Real} (hr0 : 0 ≤ r)
    (hr : r ≤ 1 / (n : Real)) :
    adaptiveRadiusQWarmFactor n (1 + r) ≤ ENNReal.ofReal (2 * Real.exp 1) := by
  have hnR : 0 < (n : Real) := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hnr : (n : Real) * r ≤ 1 := by
    calc
      (n : Real) * r ≤ (n : Real) * (1 / (n : Real)) := by gcongr
      _ = 1 := by field_simp
  have hpow : (1 + r) ^ n ≤ Real.exp 1 := by
    exact (one_add_pow_le_exp hr0 n).trans (Real.exp_le_exp.mpr hnr)
  unfold adaptiveRadiusQWarmFactor
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow (by norm_num))

#print axioms adaptiveRadiusQWarmFactor_one_add_le_two_exp

end Ttc.CVAdaptiveRadiusQSmallRateWarm
