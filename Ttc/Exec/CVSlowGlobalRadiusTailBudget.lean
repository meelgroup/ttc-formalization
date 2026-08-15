import Ttc.Exec.CVGlobalLogarithmicRadius
import Ttc.Exec.CVContinuingRetryParameters
import Ttc.Exec.CVSlowFullBodySourceSchedule
import Ttc.Exec.CVGaussianScoreAwareParameters

/-!
Run-global adjustable-radius tail accounting for the uniformly slow schedule.

The selector is scaled by the actual active stream/phase count divided by the
corrected dependence allowance.  This is stronger than merely allocating a fixed
tail budget: after summing every phase in every stream, the tail is at most `1/80`.
-/

set_option autoImplicit false

namespace Ttc.CVSlowGlobalRadiusTailBudget

open Finset
open Ttc.CVCorrected Ttc.CVGlobalLogarithmicRadius
open Ttc.CVContinuingRetryParameters
open Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVGaussianBlockRetryParameters Ttc.CVGaussianScoreAwareParameters
open scoped ENNReal BigOperators

/-- Effective global-call parameter for the slow schedule's radial tail. -/
noncomputable def slowRadiusTailCalls (m k : Nat) (eps : Real) : Real :=
  max 1 (4 * (((m * k : Nat) : Real)) / correctedNu m eps)

/-- One radius used by every slow phase and independent stream. -/
noncomputable def slowGlobalRadiusQ (n m k : Nat) (eps : Real) : Real :=
  globalLogarithmicRadiusQ n (slowRadiusTailCalls m k eps)

theorem one_le_slowRadiusTailCalls (m k : Nat) (eps : Real) :
    1 ≤ slowRadiusTailCalls m k eps := le_max_left _ _

theorem four_le_slowGlobalRadiusQ
    {n : Nat} (hn : 1 ≤ n) (m k : Nat) (eps : Real) :
    4 ≤ slowGlobalRadiusQ n m k eps := by
  exact four_le_globalLogarithmicRadiusQ hn
    (one_le_slowRadiusTailCalls m k eps)

/-- Real-valued accumulated radial tail over all `m*k` active calls. -/
theorem slowGlobalRadiusQ_activeTail_le_one_eightieth
    {n m k : Nat} (hn : 1 ≤ n) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (((m * k : Nat) : Real)) *
        (slowGlobalRadiusQ n m k eps *
          Real.exp (-(slowGlobalRadiusQ n m k eps ^ 2 - 1) / 2)) ^ n ≤
      1 / 80 := by
  let nu := correctedNu m eps
  let calls : Real := ((m * k : Nat) : Real)
  let A := slowRadiusTailCalls m k eps
  let q := slowGlobalRadiusQ n m k eps
  let tail := (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n
  have hnu : 0 < nu := correctedNu_pos heps
  have hnu1 : nu ≤ 1 := correctedNu_le_one heps heps1
  have hA1 : 1 ≤ A := one_le_slowRadiusTailCalls m k eps
  have htail0 : 0 ≤ tail := by
    dsimp only [tail, q, slowGlobalRadiusQ]
    exact pow_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) n
  have htotal : A * tail ≤ 1 / 20 := by
    dsimp only [A, q, tail, slowGlobalRadiusQ]
    exact globalLogarithmicRadiusQ_totalTail_le hn hA1
  have hbase : 4 * calls / nu ≤ A := by
    dsimp only [A, calls, slowRadiusTailCalls]
    exact le_max_right _ _
  have hsmall : (4 * calls / nu) * tail ≤ 1 / 20 :=
    (mul_le_mul_of_nonneg_right hbase htail0).trans htotal
  have hsmall' : (4 * calls * tail) / nu ≤ 1 / 20 := by
    calc
      (4 * calls * tail) / nu = (4 * calls / nu) * tail := by ring
      _ ≤ 1 / 20 := hsmall
  have hscaled : 4 * calls * tail ≤ (1 / 20) * nu :=
    (div_le_iff₀ hnu).mp hsmall'
  dsimp only [nu, calls, q, tail] at hscaled ⊢
  nlinarith

/-- ENNReal form used directly by the retained-reference error premise. -/
theorem slowGlobalRadiusQ_sum_tail_le_one_eightieth
    {n m k : Nat} (hn : 1 ≤ n) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (k : ENNReal) *
        (∑ _i ∈ range m, ENNReal.ofReal
          ((slowGlobalRadiusQ n m k eps *
            Real.exp (-(slowGlobalRadiusQ n m k eps ^ 2 - 1) / 2)) ^ n)) ≤
      ENNReal.ofReal (1 / 80 : Real) := by
  let tail : Real :=
    (slowGlobalRadiusQ n m k eps *
      Real.exp (-(slowGlobalRadiusQ n m k eps ^ 2 - 1) / 2)) ^ n
  have htail0 : 0 ≤ tail := by
    dsimp only [tail, slowGlobalRadiusQ]
    exact pow_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) n
  have hreal := slowGlobalRadiusQ_activeTail_le_one_eightieth
    (n := n) (m := m) (k := k) hn heps heps1
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ htail0)]
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [sum_const, card_range, nsmul_eq_mul, Nat.cast_mul,
    mul_assoc, mul_comm, mul_left_comm] using hreal

/-- Specialization with the active count fixed to the slow source phase count. -/
theorem slowSourceGlobalRadiusQ_sum_tail_le_one_eightieth
    {n k : Nat} (hn : 1 ≤ n) {N s0 eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (k : ENNReal) *
        (∑ _i ∈ range (slowSourcePhases n N s0), ENNReal.ofReal
          ((slowGlobalRadiusQ n (slowSourcePhases n N s0) k eps *
            Real.exp (-(slowGlobalRadiusQ n (slowSourcePhases n N s0) k eps ^ 2 - 1) /
              2)) ^ n)) ≤
      ENNReal.ofReal (1 / 80 : Real) := by
  exact slowGlobalRadiusQ_sum_tail_le_one_eightieth hn heps heps1

/-- The local score-aware operational errors, summed over all slow phases and
streams, consume at most the other `1/80` half of the reference-TV budget. -/
theorem scoreAwareMixError_sum_le_one_eightieth
    {m k : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) :
    (k : ENNReal) *
        (∑ i ∈ range m, scoreAwareMixError m k eps slack boundSq i) ≤
      ENNReal.ofReal (1 / 80 : Real) := by
  have hnu0 : 0 ≤ correctedNu m eps := correctedNu_nonneg
  have hm0 : (0 : Real) ≤ m := by positivity
  have ha1 := one_le_correctedAlpha (m := m) heps heps1
  have ha4 : 1 ≤ correctedAlpha m eps ^ 4 := one_le_pow₀ ha1
  have hdep := correctedNu_alpha_four_mul_le (m := m) (r := m)
    heps (Nat.le_succ m)
  have hcoef0 : 0 ≤ 2 * correctedNu m eps := by positivity
  have hcoef :
      2 * correctedNu m eps ≤
        2 * correctedNu m eps * correctedAlpha m eps ^ 4 := by
    calc
      2 * correctedNu m eps = (2 * correctedNu m eps) * 1 := by ring
      _ ≤ (2 * correctedNu m eps) * correctedAlpha m eps ^ 4 :=
        mul_le_mul_of_nonneg_left ha4 hcoef0
  have hmono :
      2 * correctedNu m eps * (m : Real) ≤
        2 * correctedNu m eps * correctedAlpha m eps ^ 4 * (m : Real) := by
    exact mul_le_mul_of_nonneg_right hcoef hm0
  have hmnu : (m : Real) * correctedNu m eps ≤ 1 / 100000 := by
    have heps2 : eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg eps]
    nlinarith [hmono.trans hdep]
  have hkden : 0 < (k : Real) + 1 := by positivity
  have hkfrac : (k : Real) / ((k : Real) + 1) ≤ 1 := by
    rw [div_le_one hkden]
    linarith
  have hreal :
      (k : Real) *
          (∑ i ∈ range m,
            (scoreAwareMixError m k eps slack boundSq i).toReal) ≤
        1 / 80 := by
    calc
      (k : Real) *
          (∑ i ∈ range m,
            (scoreAwareMixError m k eps slack boundSq i).toReal) ≤
          (k : Real) * (∑ _i ∈ range m,
            (3 * blockShare m k eps)) := by
              gcongr with i hi
              exact (scoreAwareMixError_toReal_le_three_share
                (m := m) (k := k) heps heps1 hslack hbound i).trans
                (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
      _ = (3 / 8) * ((k : Real) / ((k : Real) + 1)) *
          ((m : Real) * correctedNu m eps) := by
            simp only [sum_const, card_range, nsmul_eq_mul]
            unfold blockShare
            field_simp
      _ ≤ (3 / 8) * 1 * (1 / 100000) := by gcongr
      _ ≤ 1 / 80 := by norm_num
  have herrTop : ∀ i, scoreAwareMixError m k eps slack boundSq i ≠ ⊤ :=
    fun i ↦ scoreAwareMixError_ne_top m k eps slack boundSq i
  have hsumTop :
      (∑ i ∈ range m, scoreAwareMixError m k eps slack boundSq i) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.2 (fun i hi ↦ herrTop i)
  refine (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (by simp) hsumTop) ENNReal.ofReal_ne_top).mp ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun i hi ↦ herrTop i),
    ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 1 / 80)]
  exact hreal

/-- Complete accumulated full-pair TV budget: local operational error plus the
adjustable radial tail, across every phase and independent stream. -/
theorem slowGlobalRadiusQ_fullPair_sum_le_one_fortieth
    {n m k : Nat} (hn : 1 ≤ n) {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) :
    let q := slowGlobalRadiusQ n m k eps
    let tail := ENNReal.ofReal
      ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)
    (k : ENNReal) *
        (∑ i ∈ range m,
          (scoreAwareMixError m k eps slack boundSq i + tail)) ≤
      ENNReal.ofReal (1 / 40 : Real) := by
  dsimp only
  rw [sum_add_distrib, mul_add]
  calc
    (k : ENNReal) *
          (∑ i ∈ range m, scoreAwareMixError m k eps slack boundSq i) +
        (k : ENNReal) *
          (∑ _i ∈ range m, ENNReal.ofReal
            ((slowGlobalRadiusQ n m k eps *
              Real.exp (-(slowGlobalRadiusQ n m k eps ^ 2 - 1) / 2)) ^ n)) ≤
      ENNReal.ofReal (1 / 80 : Real) + ENNReal.ofReal (1 / 80 : Real) :=
        add_le_add
          (scoreAwareMixError_sum_le_one_eightieth heps heps1 hslack hbound)
          (slowGlobalRadiusQ_sum_tail_le_one_eightieth hn heps heps1)
    _ = ENNReal.ofReal (1 / 40 : Real) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : Real) ≤ 1 / 80)
        (by norm_num : (0 : Real) ≤ 1 / 80)]
      norm_num

#print axioms slowGlobalRadiusQ_activeTail_le_one_eightieth
#print axioms slowGlobalRadiusQ_sum_tail_le_one_eightieth
#print axioms slowSourceGlobalRadiusQ_sum_tail_le_one_eightieth
#print axioms scoreAwareMixError_sum_le_one_eightieth
#print axioms slowGlobalRadiusQ_fullPair_sum_le_one_fortieth

end Ttc.CVSlowGlobalRadiusTailBudget
