import Ttc.Exec.CVGaussianBlockRetryParameters

/-! Phase-dependent retry/mixing shares small enough to transport the bounded Gaussian
ratio-score second moment. -/

namespace Ttc.CVGaussianScoreAwareParameters

open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVContinuingRetryParameters
open Ttc.CVCorrected
open Ttc.CVAdaptive
open scoped ENNReal

/-- `slack i` is the available additive second-moment slack and `boundSq i` is the
TV transport multiplier.  The factor three pays for mixing, retry threshold, and the
geometric retry tail. -/
noncomputable def scoreAwareShare (m k : Nat) (eps : Real)
    (slack boundSq : Nat → Real) (i : Nat) : Real :=
  min (blockShare m k eps) (slack i / (3 * boundSq i))

noncomputable def scoreAwareZeta (m k : Nat) (eps : Real)
    (slack boundSq : Nat → Real) (i : Nat) : ENNReal :=
  ENNReal.ofReal (scoreAwareShare m k eps slack boundSq i / 32)

noncomputable def scoreAwareEta (m k : Nat) (eps : Real)
    (slack boundSq : Nat → Real) (i : Nat) : ENNReal :=
  ENNReal.ofReal (scoreAwareShare m k eps slack boundSq i)

noncomputable def scoreAwareRetries (m k : Nat) (eps : Real)
    (slack boundSq : Nat → Real) (i : Nat) : Nat :=
  16 * explicitDyadicTailIndex (scoreAwareShare m k eps slack boundSq i)

noncomputable def scoreAwareMixError (m k : Nat) (eps : Real)
    (slack boundSq : Nat → Real) (i : Nat) : ENNReal :=
  32 * scoreAwareZeta m k eps slack boundSq i +
    (scoreAwareEta m k eps slack boundSq i +
      continuingContraction ^ scoreAwareRetries m k eps slack boundSq i)

theorem scoreAwareShare_pos {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    (i : Nat) : 0 < scoreAwareShare m k eps slack boundSq i := by
  unfold scoreAwareShare
  exact lt_min (blockShare_pos heps)
    (div_pos (hslack i) (mul_pos (by norm_num) (hbound i)))

theorem scoreAwareShare_lt_one {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (i : Nat) :
    scoreAwareShare m k eps slack boundSq i < 1 :=
  (min_le_left _ _).trans_lt (blockShare_lt_one heps heps1)

theorem scoreAwareZeta_le_sixteenth
    {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (i : Nat) :
    scoreAwareZeta m k eps slack boundSq i ≤ ENNReal.ofReal (1 / 16 : Real) := by
  apply ENNReal.ofReal_le_ofReal
  have hs := scoreAwareShare_lt_one (m := m) (k := k)
    (slack := slack) (boundSq := boundSq) heps heps1 i
  linarith

theorem scoreAwareMixError_ne_top
    (m k : Nat) (eps : Real) (slack boundSq : Nat → Real) (i : Nat) :
    scoreAwareMixError m k eps slack boundSq i ≠ ⊤ := by
  unfold scoreAwareMixError scoreAwareZeta scoreAwareEta continuingContraction
  finiteness

theorem contraction_pow_scoreAwareRetries_le_eta
    {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) (i : Nat) :
    continuingContraction ^ scoreAwareRetries m k eps slack boundSq i ≤
      scoreAwareEta m k eps slack boundSq i := by
  let s := scoreAwareShare m k eps slack boundSq i
  let j := explicitDyadicTailIndex s
  have hpow : ((15 / 16 : Real) ^ 16) ^ j ≤ ((1 / 2 : Real)) ^ j :=
    pow_le_pow_left₀ (by positivity) contraction_pow_sixteen_le_half j
  have hdyadic : (1 / 2 : Real) ^ j ≤ s := by
    simpa only [one_div, inv_pow] using
      (inv_two_pow_explicitDyadicTailIndex_le
        (show 0 < s from scoreAwareShare_pos heps hslack hbound i)
        (show s < 1 from scoreAwareShare_lt_one heps heps1 i))
  rw [continuingContraction, scoreAwareRetries, scoreAwareEta, ← ENNReal.ofReal_pow]
  apply ENNReal.ofReal_le_ofReal
  rw [pow_mul]
  exact hpow.trans hdyadic
  norm_num

/-- The whole operational TV error is at most three times the selected real share. -/
theorem scoreAwareMixError_toReal_le_three_share
    {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) (i : Nat) :
    (scoreAwareMixError m k eps slack boundSq i).toReal ≤
      3 * scoreAwareShare m k eps slack boundSq i := by
  have hs0 : 0 ≤ scoreAwareShare m k eps slack boundSq i :=
    (scoreAwareShare_pos heps hslack hbound i).le
  have htail := contraction_pow_scoreAwareRetries_le_eta
    (m := m) (k := k) heps heps1 hslack hbound i
  have htailTop : continuingContraction ^
      scoreAwareRetries m k eps slack boundSq i ≠ ⊤ := by
    unfold continuingContraction
    finiteness
  have hetaTop : scoreAwareEta m k eps slack boundSq i ≠ ⊤ := ENNReal.ofReal_ne_top
  have hzetaTop : scoreAwareZeta m k eps slack boundSq i ≠ ⊤ := by
    unfold scoreAwareZeta
    exact ENNReal.ofReal_ne_top
  have hmulTop : (32 : ENNReal) * scoreAwareZeta m k eps slack boundSq i ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hzetaTop
  have hinnerTop : scoreAwareEta m k eps slack boundSq i +
      continuingContraction ^ scoreAwareRetries m k eps slack boundSq i ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hetaTop, htailTop⟩
  have htailReal : (continuingContraction ^
      scoreAwareRetries m k eps slack boundSq i).toReal ≤
      scoreAwareShare m k eps slack boundSq i := by
    simpa only [scoreAwareEta, ENNReal.toReal_ofReal hs0] using
      ((ENNReal.toReal_le_toReal htailTop hetaTop).2 htail)
  rw [scoreAwareMixError, ENNReal.toReal_add hmulTop hinnerTop, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_add hetaTop htailTop, scoreAwareZeta, scoreAwareEta,
    ENNReal.toReal_ofReal (div_nonneg hs0 (by norm_num)),
    ENNReal.toReal_ofReal hs0]
  nlinarith

/-- The score-aware choice discharges precisely the formerly missing TV moment slack. -/
theorem scoreAwareMixError_mul_boundSq_le_slack
    {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) (i : Nat) :
    (scoreAwareMixError m k eps slack boundSq i).toReal * boundSq i ≤ slack i := by
  have hm := scoreAwareMixError_toReal_le_three_share
    (m := m) (k := k) heps heps1 hslack hbound i
  have hs := min_le_right (blockShare m k eps) (slack i / (3 * boundSq i))
  change scoreAwareShare m k eps slack boundSq i ≤ _ at hs
  have hb := (hbound i).le
  calc
    (scoreAwareMixError m k eps slack boundSq i).toReal * boundSq i ≤
        (3 * scoreAwareShare m k eps slack boundSq i) * boundSq i := by
          exact mul_le_mul_of_nonneg_right hm hb
    _ ≤ (3 * (slack i / (3 * boundSq i))) * boundSq i := by
          gcongr
    _ = slack i := by field_simp [(hbound i).ne']

/-- Shrinking the scalar share retains the independent-stream dependence budget. -/
theorem scoreAwareMixError_budget
    {m k : Nat} {eps : Real} {slack boundSq : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) (i : Nat) :
    (k : Real) * (2 * (scoreAwareMixError m k eps slack boundSq i).toReal) ≤
      correctedNu m eps := by
  have hm := scoreAwareMixError_toReal_le_three_share
    (m := m) (k := k) heps heps1 hslack hbound i
  have hs : scoreAwareShare m k eps slack boundSq i ≤ blockShare m k eps :=
    min_le_left _ _
  have hnu0 := (correctedNu_pos (m := m) heps).le
  have hk0 : (0 : Real) ≤ k := by positivity
  calc
    (k : Real) * (2 * (scoreAwareMixError m k eps slack boundSq i).toReal) ≤
        (k : Real) * (2 * (3 * scoreAwareShare m k eps slack boundSq i)) := by
          gcongr
    _ ≤ (k : Real) * (2 * (3 * blockShare m k eps)) := by gcongr
    _ ≤ correctedNu m eps := by
      unfold blockShare
      have hk : (k : Real) ≤ k + 1 := by linarith
      have hden : 0 < 8 * ((k : Real) + 1) := by positivity
      have hfrac : 6 * (k : Real) / (8 * ((k : Real) + 1)) ≤ 1 := by
        rw [div_le_one hden]
        nlinarith
      calc
        (k : Real) * (2 * (3 * (correctedNu m eps / (8 * ((k : Real) + 1))))) =
            (6 * (k : Real) / (8 * ((k : Real) + 1))) * correctedNu m eps := by ring
        _ ≤ 1 * correctedNu m eps := mul_le_mul_of_nonneg_right hfrac hnu0
        _ = correctedNu m eps := one_mul _

#print axioms contraction_pow_scoreAwareRetries_le_eta
#print axioms scoreAwareZeta_le_sixteenth
#print axioms scoreAwareMixError_ne_top
#print axioms scoreAwareMixError_toReal_le_three_share
#print axioms scoreAwareMixError_mul_boundSq_le_slack
#print axioms scoreAwareMixError_budget

end Ttc.CVGaussianScoreAwareParameters
