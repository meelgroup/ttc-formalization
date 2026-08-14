/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.MomentRadiusMarkovTruncation

/-!
# A polynomial moment-radius parameter without LV07 concentration

The exact Cousins--Vempala rate uses the LV07 exponential norm tail.  Until that analytic
lemma is formalized, Markov's inequality still gives an unconditional bounded-body
reduction.  This file packages its enclosing-radius parameter and proves that the adaptive
runtime target `C² n` is at most `2n + 2R²/eta`.  Consequently this route is polynomial in
`n`, `R`, and `1/eta`, although it loses one accuracy factor compared with Theorem 1.1.
-/

namespace Ttc.CVAdaptive

open Metric Set

variable {n : Nat}

/-- Dimension-normalized enclosing radius for the Markov-truncated body. -/
noncomputable def markovRuntimeC (n : Nat) (R eta : Real) : Real :=
  max 1 (markovMomentTruncationRadius R eta / Real.sqrt n)

theorem one_le_markovRuntimeC (n : Nat) (R eta : Real) :
    1 <= markovRuntimeC n R eta := le_max_left _ _

theorem markovRuntimeC_pos (n : Nat) (R eta : Real) :
    0 < markovRuntimeC n R eta := one_pos.trans_le (one_le_markovRuntimeC n R eta)

/-- The Markov truncation ball fits the `C*sqrt n` geometry used by the adaptive sampler. -/
theorem markovMomentTruncationRadius_le_C_sqrt_n
    (hn : 1 <= n) {R eta : Real} :
    markovMomentTruncationRadius R eta <=
      markovRuntimeC n R eta * Real.sqrt n := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (Nat.zero_lt_of_lt hn))
  have hle : markovMomentTruncationRadius R eta / Real.sqrt n <=
      markovRuntimeC n R eta := le_max_right _ _
  apply (div_le_iff₀ hsn).1
  simpa [mul_comm] using hle

theorem inter_markovBall_subset_runtimeBall
    (hn : 1 <= n) {K : Set (EuclideanSpace Real (Fin n))}
    {R eta : Real} :
    K ∩ closedBall 0 (markovMomentTruncationRadius R eta) ⊆
      closedBall 0 (markovRuntimeC n R eta * Real.sqrt n) := by
  intro x hx
  exact mem_closedBall'.2 ((mem_closedBall'.1 hx.2).trans
    (markovMomentTruncationRadius_le_C_sqrt_n hn))

/-- The squared adaptive target is polynomial under the unconditional Markov truncation. -/
theorem markovRuntimeC_sq_mul_n_le
    (hn : 1 <= n) {R eta : Real} (hR : 0 < R) (heta : 0 < eta) :
    markovRuntimeC n R eta ^ 2 * (n : Real) <=
      2 * (n : Real) + 2 * R ^ 2 / eta := by
  have hn0 : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hetaS : 0 < Real.sqrt eta := Real.sqrt_pos.2 heta
  have hr : 0 < markovMomentTruncationRadius R eta :=
    markovMomentTruncationRadius_pos hR heta
  have hratio0 : 0 <= markovMomentTruncationRadius R eta / Real.sqrt n := by positivity
  have hmax : markovRuntimeC n R eta <=
      1 + markovMomentTruncationRadius R eta / Real.sqrt n := by
    unfold markovRuntimeC
    exact max_le (by linarith) (by linarith)
  have hC0 : 0 <= markovRuntimeC n R eta := (markovRuntimeC_pos n R eta).le
  have hsq : markovRuntimeC n R eta ^ 2 <=
      2 + 2 * (markovMomentTruncationRadius R eta / Real.sqrt n) ^ 2 := by
    calc
      markovRuntimeC n R eta ^ 2 <=
          (1 + markovMomentTruncationRadius R eta / Real.sqrt n) ^ 2 := by nlinarith
      _ <= 2 + 2 * (markovMomentTruncationRadius R eta / Real.sqrt n) ^ 2 := by
        nlinarith [sq_nonneg (1 - markovMomentTruncationRadius R eta / Real.sqrt n)]
  have hsn2 : Real.sqrt n ^ 2 = (n : Real) := Real.sq_sqrt hn0.le
  have heta2 : Real.sqrt eta ^ 2 = eta := Real.sq_sqrt heta.le
  calc
    markovRuntimeC n R eta ^ 2 * (n : Real) <=
        (2 + 2 * (markovMomentTruncationRadius R eta / Real.sqrt n) ^ 2) * n := by
      gcongr
    _ = 2 * (n : Real) + 2 * R ^ 2 / eta := by
      unfold markovMomentTruncationRadius
      rw [add_mul]
      congr 1
      rw [div_pow, div_pow, hsn2, heta2]
      field_simp [hn0.ne', heta.ne']

#print axioms markovMomentTruncationRadius_le_C_sqrt_n
#print axioms inter_markovBall_subset_runtimeBall
#print axioms markovRuntimeC_sq_mul_n_le

end Ttc.CVAdaptive
