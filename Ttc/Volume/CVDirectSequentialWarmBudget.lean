/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVDirectSequentialWarm
import Arlib.MarkovChains.Continuous.WarmLSMixing

/-!
# Logarithmic mixing price of accumulated sequential warmness

The direct cooling trajectory can be `M₀ * e^i`-warm at phase `i`.  This file records the
important runtime fact that the Lovász--Simonovits deadline sees only the logarithm of this
quantity, and hence grows linearly with the phase index.
-/

namespace Ttc.CVDirectSequentialWarm

open Arlib.MarkovChains
open scoped ENNReal

/-- `accumulatedWarm` agrees with the real geometric warmness budget under `ofReal`. -/
theorem accumulatedWarm_ofReal {M C : Real} (hM : 0 <= M) (hC : 0 <= C) (i : Nat) :
    accumulatedWarm (ENNReal.ofReal M) (ENNReal.ofReal C) i =
      ENNReal.ofReal (M * C ^ i) := by
  rw [accumulatedWarm, ENNReal.ofReal_mul hM, ENNReal.ofReal_pow hC]

/-- For the consecutive-phase factor `e`, the log warmness price is exactly linear. -/
theorem log_realAccumulatedWarm_exp {M : Real} (hM : 0 < M) (i : Nat) :
    Real.log (M * Real.exp 1 ^ i) = Real.log M + i := by
  rw [Real.log_mul hM.ne' (pow_ne_zero _ (Real.exp_ne_zero 1)), Real.log_pow,
    Real.log_exp]
  norm_num

/-- Exact LS deadline after substituting the sequential budget `M * e^i`. -/
theorem lsThresholdS_realAccumulatedWarm_exp {M phi eps : Real}
    (hM : 0 < M) (heps : 0 < eps) (i : Nat) :
    lsThresholdS (M * Real.exp 1 ^ i) phi eps =
      2 * (Real.log (2 * M / eps) + i) / phi ^ 2 := by
  unfold lsThresholdS
  have hbase : 0 < 2 * M / eps := by positivity
  rw [show 2 * (M * Real.exp 1 ^ i) / eps = (2 * M / eps) * Real.exp 1 ^ i by
      field_simp,
    Real.log_mul hbase.ne' (pow_ne_zero _ (Real.exp_ne_zero 1)), Real.log_pow,
    Real.log_exp]
  norm_num

/-- A phase-count bound turns accumulated warmth into a linear deadline bound. -/
theorem lsThresholdS_realAccumulatedWarm_exp_le {M phi eps P : Real}
    (hM : 0 < M) (heps : 0 < eps) {i : Nat}
    (hi : (i : Real) <= P) :
    lsThresholdS (M * Real.exp 1 ^ i) phi eps <=
      2 * (Real.log (2 * M / eps) + P) / phi ^ 2 := by
  rw [lsThresholdS_realAccumulatedWarm_exp hM heps]
  have hadd : Real.log (2 * M / eps) + (i : Real) ≤
      Real.log (2 * M / eps) + P := by linarith
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hadd (by norm_num))
    (sq_nonneg phi)

end Ttc.CVDirectSequentialWarm

#print axioms Ttc.CVDirectSequentialWarm.accumulatedWarm_ofReal
#print axioms Ttc.CVDirectSequentialWarm.log_realAccumulatedWarm_exp
#print axioms Ttc.CVDirectSequentialWarm.lsThresholdS_realAccumulatedWarm_exp
#print axioms Ttc.CVDirectSequentialWarm.lsThresholdS_realAccumulatedWarm_exp_le
