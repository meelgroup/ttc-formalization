import Ttc.Exec.CVHybridRadiusQCanonicalOperational
import Ttc.Exec.CVGlobalLogarithmicRadius
import Ttc.Exec.CVGaussianScoreAwareParameters

/-! Allocate the selected-radius truncation tail inside the independent-stream budget. -/

set_option autoImplicit false

namespace Ttc.CVGlobalRadiusDependenceBudget

open Ttc.CVCorrected Ttc.CVGaussianBlockRetryParameters
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVContinuingRetryParameters
open Ttc.CVHybridRadiusQCanonicalOperational
open Ttc.CVGlobalLogarithmicRadius
open scoped ENNReal

/-- Effective call count chosen so one radial tail spends precisely the unused quarter
of the score-aware independent-stream dependence allowance. -/
noncomputable def dependenceRadiusCalls (m k : Nat) (eps : Real) : Real :=
  max 1 (2 * ((k : Real) + 1) / (5 * correctedNu m eps))

theorem one_le_dependenceRadiusCalls (m k : Nat) (eps : Real) :
    1 ≤ dependenceRadiusCalls m k eps := le_max_left _ _

theorem dependenceRadiusTail_le
    {n m k : Nat} (hn : 1 ≤ n) {eps : Real} (heps : 0 < eps) :
    (globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps) *
        Real.exp (-(globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps) ^ 2 - 1) / 2)) ^ n ≤
      correctedNu m eps / (8 * ((k : Real) + 1)) := by
  let nu := correctedNu m eps
  let kp : Real := (k : Real) + 1
  let A := dependenceRadiusCalls m k eps
  let t := (globalLogarithmicRadiusQ n A *
    Real.exp (-(globalLogarithmicRadiusQ n A ^ 2 - 1) / 2)) ^ n
  have hnu : 0 < nu := correctedNu_pos heps
  have hkp : 0 < kp := by dsimp only [kp]; positivity
  have hA1 : 1 ≤ A := by exact one_le_dependenceRadiusCalls m k eps
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    exact pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) n
  have htotal : A * t ≤ 1 / 20 := by
    exact globalLogarithmicRadiusQ_totalTail_le hn hA1
  have hbase : 2 * kp / (5 * nu) ≤ A := by
    dsimp only [A, dependenceRadiusCalls]
    exact le_max_right _ _
  have hsmall : (2 * kp / (5 * nu)) * t ≤ 1 / 20 :=
    (mul_le_mul_of_nonneg_right hbase ht0).trans htotal
  have hscaled : 8 * kp * t ≤ nu := by
    have hden : 0 < 5 * nu := by positivity
    have h := (div_le_iff₀ hden).mp (by
      simpa only [div_mul_eq_mul_div, mul_assoc] using hsmall)
    nlinarith
  dsimp only [nu, kp, A, t] at hscaled ⊢
  apply (le_div_iff₀ (by positivity : 0 < 8 * ((k : Real) + 1))).2
  simpa only [mul_comm] using hscaled

/-- The local score-aware error plus selected-radius tail satisfies the exact
`k`-stream dependence budget. -/
theorem hybridRadiusQCanonicalMixError_scoreAware_budget
    {n m k : Nat} (hn : 1 ≤ n) {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) (i : Nat) :
    let A := dependenceRadiusCalls m k eps
    let q := globalLogarithmicRadiusQ n A
    (k : Real) * (2 *
      (hybridRadiusQCanonicalMixError n q
        (scoreAwareEta m k eps slack boundSq)
        (scoreAwareZeta m k eps slack boundSq)
        (scoreAwareRetries m k eps slack boundSq) i).toReal) ≤ correctedNu m eps := by
  dsimp only
  let q := globalLogarithmicRadiusQ n (dependenceRadiusCalls m k eps)
  let tail : Real :=
    (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n
  have htail0 : 0 ≤ tail := by
    dsimp only [tail, q]
    exact pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) n
  have htail := dependenceRadiusTail_le (n := n) (m := m) (k := k) hn heps
  have hlocal := scoreAwareMixError_toReal_le_three_share
    (m := m) (k := k) heps heps1 hslack hbound i
  have hshare : scoreAwareShare m k eps slack boundSq i ≤ blockShare m k eps :=
    min_le_left _ _
  have hnu0 := (correctedNu_pos (m := m) heps).le
  have hk0 : (0 : Real) ≤ k := by positivity
  have herrTop := scoreAwareMixError_ne_top m k eps slack boundSq i
  have htailTop : ENNReal.ofReal tail ≠ ⊤ := ENNReal.ofReal_ne_top
  have hreal :
      (hybridRadiusQCanonicalMixError n q
        (scoreAwareEta m k eps slack boundSq)
        (scoreAwareZeta m k eps slack boundSq)
        (scoreAwareRetries m k eps slack boundSq) i).toReal =
      (scoreAwareMixError m k eps slack boundSq i).toReal + tail := by
    change (scoreAwareMixError m k eps slack boundSq i +
      ENNReal.ofReal tail).toReal = _
    rw [ENNReal.toReal_add herrTop htailTop, ENNReal.toReal_ofReal htail0]
  rw [hreal]
  calc
    (k : Real) * (2 * ((scoreAwareMixError m k eps slack boundSq i).toReal + tail)) ≤
        (k : Real) * (2 * (3 * blockShare m k eps +
          correctedNu m eps / (8 * ((k : Real) + 1)))) := by
            gcongr
            · exact hlocal.trans (mul_le_mul_of_nonneg_left hshare (by norm_num))
    _ ≤ correctedNu m eps := by
      unfold blockShare
      have hden : 0 < 8 * ((k : Real) + 1) := by positivity
      have hfrac : (8 * (k : Real)) / (8 * ((k : Real) + 1)) ≤ 1 := by
        rw [div_le_one hden]
        nlinarith
      calc
        (k : Real) * (2 *
          (3 * (correctedNu m eps / (8 * ((k : Real) + 1))) +
            correctedNu m eps / (8 * ((k : Real) + 1)))) =
          ((8 * (k : Real)) / (8 * ((k : Real) + 1))) * correctedNu m eps := by ring
        _ ≤ 1 * correctedNu m eps := mul_le_mul_of_nonneg_right hfrac hnu0
        _ = correctedNu m eps := one_mul _

/-- Radius-agnostic form of the same allocation: any selected radius whose real tail
fits the unused quarter-share can be plugged into the canonical operation. -/
theorem hybridRadiusQCanonicalMixError_scoreAware_budget_of_tail
    {n m k : Nat} {q eps : Real} (hq0 : 0 ≤ q)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    (htail : (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n ≤
      correctedNu m eps / (8 * ((k : Real) + 1))) (i : Nat) :
    (k : Real) * (2 *
      (hybridRadiusQCanonicalMixError n q
        (scoreAwareEta m k eps slack boundSq)
        (scoreAwareZeta m k eps slack boundSq)
        (scoreAwareRetries m k eps slack boundSq) i).toReal) ≤ correctedNu m eps := by
  let tail : Real := (q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n
  have htail0 : 0 ≤ tail := by
    dsimp only [tail]
    exact pow_nonneg (mul_nonneg hq0 (Real.exp_pos _).le) n
  have hlocal := scoreAwareMixError_toReal_le_three_share
    (m := m) (k := k) heps heps1 hslack hbound i
  have hshare : scoreAwareShare m k eps slack boundSq i ≤ blockShare m k eps :=
    min_le_left _ _
  have hnu0 := (correctedNu_pos (m := m) heps).le
  have herrTop := scoreAwareMixError_ne_top m k eps slack boundSq i
  have htailTop : ENNReal.ofReal tail ≠ ⊤ := ENNReal.ofReal_ne_top
  have hreal :
      (hybridRadiusQCanonicalMixError n q
        (scoreAwareEta m k eps slack boundSq)
        (scoreAwareZeta m k eps slack boundSq)
        (scoreAwareRetries m k eps slack boundSq) i).toReal =
      (scoreAwareMixError m k eps slack boundSq i).toReal + tail := by
    change (scoreAwareMixError m k eps slack boundSq i +
      ENNReal.ofReal tail).toReal = _
    rw [ENNReal.toReal_add herrTop htailTop, ENNReal.toReal_ofReal htail0]
  rw [hreal]
  calc
    (k : Real) * (2 * ((scoreAwareMixError m k eps slack boundSq i).toReal + tail)) ≤
        (k : Real) * (2 * (3 * blockShare m k eps +
          correctedNu m eps / (8 * ((k : Real) + 1)))) := by
            gcongr
            · exact hlocal.trans (mul_le_mul_of_nonneg_left hshare (by norm_num))
    _ ≤ correctedNu m eps := by
      unfold blockShare
      have hden : 0 < 8 * ((k : Real) + 1) := by positivity
      have hfrac : (8 * (k : Real)) / (8 * ((k : Real) + 1)) ≤ 1 := by
        rw [div_le_one hden]
        nlinarith
      calc
        (k : Real) * (2 *
          (3 * (correctedNu m eps / (8 * ((k : Real) + 1))) +
            correctedNu m eps / (8 * ((k : Real) + 1)))) =
          ((8 * (k : Real)) / (8 * ((k : Real) + 1))) * correctedNu m eps := by ring
        _ ≤ 1 * correctedNu m eps := mul_le_mul_of_nonneg_right hfrac hnu0
        _ = correctedNu m eps := one_mul _

#print axioms dependenceRadiusTail_le
#print axioms hybridRadiusQCanonicalMixError_scoreAware_budget
#print axioms hybridRadiusQCanonicalMixError_scoreAware_budget_of_tail

end Ttc.CVGlobalRadiusDependenceBudget
