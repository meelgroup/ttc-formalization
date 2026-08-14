/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVHybridSchedule
import Arlib.Convexity.GaussianCooling.ChunkedVarianceUnconditional

/-!
# Variance budget of the source two-regime schedule

The cold block pays the paper's fixed-rate factor `1 + 2/(kn)` per phase.  The hot block
pays the already-proved adaptive factor.  This file proves that their exact concatenated
product is bounded by one exponential budget, with no independence or sampler assumption.
-/

namespace Ttc.CVHybridSchedule

open scoped BigOperators
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive Ttc.CVAdaptive

/-- Cooling rate at a global hybrid phase. -/
noncomputable def phaseRate (n : Nat) (N s0 : Real) (i : Nat) : Real :=
  if i < coldPhases n s0 then 1 / (n : Real)
  else adaptivePhaseRate N (coldEnd n s0) (i - coldPhases n s0)

/-- Averaged relative-second-moment comparison factor at a global phase. -/
noncomputable def phaseVarFactor (n : Nat) (k N s0 : Real) (i : Nat) : Real :=
  if i < coldPhases n s0 then 1 + 2 / (k * (n : Real))
  else adaptiveGlobalPhaseVarFactor k N (coldEnd n s0) (i - coldPhases n s0)

/-- Averaging `k` iid scores converts the raw (`k=1`) hybrid factor into the factor whose
sample count is `k`, in both schedule regimes. -/
theorem averaged_phaseVarFactor_eq {n : Nat} {k N s0 : Real} (i : Nat) :
    1 + (phaseVarFactor n 1 N s0 i - 1) / k = phaseVarFactor n k N s0 i := by
  by_cases hi : i < coldPhases n s0
  · rw [phaseVarFactor, if_pos hi, phaseVarFactor, if_pos hi]
    ring
  · rw [phaseVarFactor, if_neg hi, phaseVarFactor, if_neg hi]
    unfold adaptiveGlobalPhaseVarFactor
    ring

/-- The hybrid variance schedule obeys its advertised rate at every successor, including
the fixed/adaptive boundary. -/
theorem sigmaSq_succ {n : Nat} (hn : 1 <= n) {N s0 : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (i : Nat) :
    sigmaSq n N s0 (i + 1) = sigmaSq n N s0 i *
      (1 + phaseRate n N s0 i) := by
  by_cases hi : i < coldPhases n s0
  · by_cases his : i + 1 < coldPhases n s0
    · rw [sigmaSq, if_pos his, sigmaSq, if_pos hi, phaseRate, if_pos hi]
      simp only [geomSchedule, pow_succ]
      ring
    · have hieq : i + 1 = coldPhases n s0 := by omega
      rw [hieq, sigmaSq_cold_boundary hn hN hs0, sigmaSq, if_pos hi,
        phaseRate, if_pos hi]
      unfold coldEnd geomSchedule
      rw [show coldPhases n s0 = i + 1 by omega, pow_succ]
      ring
  · have his : ¬ i + 1 < coldPhases n s0 := by omega
    rw [sigmaSq, if_neg his, sigmaSq, if_neg hi, phaseRate, if_neg hi]
    have hsub : i + 1 - coldPhases n s0 =
        (i - coldPhases n s0) + 1 := by omega
    rw [hsub, adaptiveSigmaSq_succ_eq_phaseRate hN (coldEnd_pos hn hs0)]

/-- Exact factorization of the finite hybrid product into its fixed and adaptive blocks. -/
theorem prod_phaseVarFactor_eq (n : Nat) {k N s0 : Real} (J : Nat) :
    ∏ i ∈ Finset.range (coldPhases n s0 + adaptiveChunkOffset N (coldEnd n s0) J),
        phaseVarFactor n k N s0 i =
      (1 + 2 / (k * (n : Real))) ^ coldPhases n s0 *
        ∏ i ∈ Finset.range (adaptiveChunkOffset N (coldEnd n s0) J),
          adaptiveGlobalPhaseVarFactor k N (coldEnd n s0) i := by
  rw [Finset.prod_range_add]
  congr 1
  · calc
      ∏ i ∈ Finset.range (coldPhases n s0), phaseVarFactor n k N s0 i =
          ∏ _i ∈ Finset.range (coldPhases n s0),
            (1 + 2 / (k * (n : Real))) := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [phaseVarFactor, if_pos (Finset.mem_range.1 hi)]
      _ = _ := by simp
  · apply Finset.prod_congr rfl
    intro i hi
    rw [phaseVarFactor, if_neg (by omega), Nat.add_sub_cancel_left]

/-- The fixed block consumes `kappaCold` of logarithmic variance budget. -/
theorem cold_prod_le_exp {n : Nat} (hn : 1 <= n) {k s0 kappaCold : Real}
    (hk : 0 < k) (hbudget :
      2 * (coldPhases n s0 : Real) / (n : Real) <= k * kappaCold) :
    (1 + 2 / (k * (n : Real))) ^ coldPhases n s0 <= Real.exp kappaCold := by
  have hnR : (0 : Real) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hx : 0 <= 2 / (k * (n : Real)) := by positivity
  have hpow := one_add_pow_le_exp hx (coldPhases n s0)
  have hexpArg : (coldPhases n s0 : Real) * (2 / (k * (n : Real))) <=
      kappaCold := by
    calc
      (coldPhases n s0 : Real) * (2 / (k * (n : Real))) =
          (2 * (coldPhases n s0 : Real) / (n : Real)) / k := by ring
      _ <= kappaCold := (div_le_iff₀ hk).2 (by simpa [mul_comm] using hbudget)
  exact hpow.trans (Real.exp_le_exp.2 hexpArg)

/-- Complete source-schedule variance budget.  The cold fixed block and hot adaptive block
add in the exponent. -/
theorem prod_phaseVarFactor_le_exp {n : Nat} (hn : 1 <= n)
    {k N s0 kappaCold kappaHot : Real} {J : Nat}
    (hk42 : 42 <= k) (hN : 0 < N) (hs0 : 0 < s0)
    (hcoldBudget : 2 * (coldPhases n s0 : Real) / (n : Real) <= k * kappaCold)
    (hbelow : ∀ j < J, adaptiveChunkStart N (coldEnd n s0) j <= N)
    (hhotBudget : 7 * (J : Real) <= k * kappaHot) :
    ∏ i ∈ Finset.range (coldPhases n s0 +
        adaptiveChunkOffset N (coldEnd n s0) J),
        phaseVarFactor n k N s0 i <= Real.exp (kappaCold + kappaHot) := by
  rw [prod_phaseVarFactor_eq n J, Real.exp_add]
  have hk : 0 < k := lt_of_lt_of_le (by norm_num) hk42
  have hcold := cold_prod_le_exp hn hk hcoldBudget
  have hhot := prod_globalPhaseVarFactor_le_exp hk42 hN (coldEnd_pos hn hs0)
    hbelow hhotBudget
  have hhot0 : 0 <= ∏ i ∈ Finset.range
      (adaptiveChunkOffset N (coldEnd n s0) J),
      adaptiveGlobalPhaseVarFactor k N (coldEnd n s0) i := by
    apply Finset.prod_nonneg
    intro i hi
    unfold adaptiveGlobalPhaseVarFactor
    have hsigma := adaptiveSigmaSq_pos hN (coldEnd_pos hn hs0) i
    positivity
  calc
    (1 + 2 / (k * (n : Real))) ^ coldPhases n s0 *
        ∏ i ∈ Finset.range (adaptiveChunkOffset N (coldEnd n s0) J),
          adaptiveGlobalPhaseVarFactor k N (coldEnd n s0) i
      <= Real.exp kappaCold *
        ∏ i ∈ Finset.range (adaptiveChunkOffset N (coldEnd n s0) J),
          adaptiveGlobalPhaseVarFactor k N (coldEnd n s0) i :=
        mul_le_mul_of_nonneg_right hcold hhot0
    _ <= Real.exp kappaCold * Real.exp kappaHot :=
        mul_le_mul_of_nonneg_left hhot (Real.exp_pos _).le

end Ttc.CVHybridSchedule

#print axioms Ttc.CVHybridSchedule.sigmaSq_succ
#print axioms Ttc.CVHybridSchedule.averaged_phaseVarFactor_eq
#print axioms Ttc.CVHybridSchedule.prod_phaseVarFactor_eq
#print axioms Ttc.CVHybridSchedule.prod_phaseVarFactor_le_exp
