import Ttc.Exec.CVGlobalLogarithmicRadius

/-! A reusable R-aware selector for phasewise Gaussian truncation tails. -/

namespace Ttc.CVPhasewiseRadiusTail

open Ttc.CVGlobalLogarithmicRadius

noncomputable def amplificationCalls (H target : Real) : Real :=
  max 1 (H / (20 * target))

theorem phasewise_tail_le_of_amplification
    {n : Nat} (hn : 1 ≤ n) {H target : Real}
    (hH : 0 < H) (htarget : 0 < target) :
    H * (globalLogarithmicRadiusQ n (amplificationCalls H target) *
      Real.exp (-(globalLogarithmicRadiusQ n (amplificationCalls H target)^2 - 1) / 2))^n
      ≤ target := by
  let A := amplificationCalls H target
  have hA : 1 ≤ A := by
    exact le_max_left _ _
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hq : 0 < globalLogarithmicRadiusQ n A :=
    lt_of_lt_of_le (by norm_num) (four_le_globalLogarithmicRadiusQ hn hA)
  have htail := globalLogarithmicRadiusQ_totalTail_le hn hA
  have htail0 : 0 ≤ (globalLogarithmicRadiusQ n A *
      Real.exp (-(globalLogarithmicRadiusQ n A ^ 2 - 1) / 2)) ^ n := by
    exact pow_nonneg (mul_nonneg hq.le (Real.exp_pos _).le) n
  have htail' : (globalLogarithmicRadiusQ n A *
      Real.exp (-(globalLogarithmicRadiusQ n A ^ 2 - 1) / 2)) ^ n ≤
      1 / (20 * A) := by
    apply (le_div_iff₀ (by positivity : (0 : Real) < 20 * A)).2
    nlinarith [htail]
  have hA2 : H / (20 * target) ≤ A := le_max_right _ _
  have htarget0 : 0 < 20 * target := by positivity
  have hmul : H ≤ 20 * target * A := by
    have := (div_le_iff₀ htarget0).1 hA2
    nlinarith
  calc
    H * (globalLogarithmicRadiusQ n A *
        Real.exp (-(globalLogarithmicRadiusQ n A ^ 2 - 1) / 2)) ^ n
        ≤ (20 * target * A) *
          (globalLogarithmicRadiusQ n A *
            Real.exp (-(globalLogarithmicRadiusQ n A ^ 2 - 1) / 2)) ^ n := by
              gcongr
    _ ≤ (20 * target * A) * (1 / (20 * A)) := by gcongr
    _ = target := by field_simp [ne_of_gt hA0]

#print axioms phasewise_tail_le_of_amplification

end Ttc.CVPhasewiseRadiusTail
