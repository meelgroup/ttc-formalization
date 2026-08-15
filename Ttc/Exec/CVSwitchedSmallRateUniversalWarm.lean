import Ttc.Exec.CVHybridRadiusQSwitchWarm

/-! Constant switched graph warmth under a globally slow cooling rate. -/

set_option autoImplicit false

namespace Ttc.CVSwitchedSmallRateUniversalWarm

open Arlib Arlib.GaussianCooling
open Ttc.CVHybridSchedule
open Ttc.CVAdaptiveRadiusQSmallRateWarm
open Ttc.CVGaussianAdaptiveAcceptedWarm
open Ttc.CVHybridRadiusQSwitchWarm
open scoped ENNReal

/-- The full-body graph factor is also at most `2e` at rate `1/n`. -/
theorem acceleratedSeedWarmFactor_one_add_le_two_exp
    {n : Nat} (hn : 1 ≤ n) {r : Real} (hr0 : 0 ≤ r)
    (hr : r ≤ 1 / (n : Real)) :
    acceleratedSeedWarmFactor n (1 + r) ≤
      ENNReal.ofReal (2 * Real.exp 1) := by
  have hnR : 0 < (n : Real) := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hnr : (n : Real) * r ≤ 1 := by
    calc
      (n : Real) * r ≤ (n : Real) * (1 / (n : Real)) := by gcongr
      _ = 1 := by field_simp
  have hpow : (1 + r) ^ n ≤ Real.exp 1 :=
    (one_add_pow_le_exp hr0 n).trans (Real.exp_le_exp.mpr hnr)
  have hone : 1 ≤ 1 + r := by linarith
  have hsqrt : Real.sqrt (1 + r) ≤ 1 + r := by
    nlinarith [Real.sq_sqrt (zero_le_one.trans hone),
      Real.sqrt_nonneg (1 + r)]
  unfold acceleratedSeedWarmFactor
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    ((pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt n).trans hpow) (by norm_num)

/-- Whichever side of the radius switch is active, a globally `1/n`-slow schedule
has the universal graph warm factor `2e`. -/
theorem switchedRadiusQWarmFactor_le_two_exp_of_rate
    {n : Nat} (hn : 1 ≤ n) {q N s0 : Real} {K : Set (EuclideanSpace Real (Fin n))}
    (i : Nat) (hrate0 : 0 ≤ phaseRate n N s0 i)
    (hrate : phaseRate n N s0 i ≤ 1 / (n : Real)) :
    switchedRadiusQWarmFactor n q N s0 K i ≤
      ENNReal.ofReal (2 * Real.exp 1) := by
  unfold switchedRadiusQWarmFactor
  split
  · exact acceleratedSeedWarmFactor_one_add_le_two_exp hn hrate0 hrate
  · exact adaptiveRadiusQWarmFactor_one_add_le_two_exp hn hrate0 hrate

#print axioms acceleratedSeedWarmFactor_one_add_le_two_exp
#print axioms switchedRadiusQWarmFactor_le_two_exp_of_rate

end Ttc.CVSwitchedSmallRateUniversalWarm
