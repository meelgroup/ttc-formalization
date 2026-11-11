import Kr25Ssmxt.Analysis.UnionLatticeNonempty
import Kr25Ssmxt.Analysis.ThinningCosts

/-! The paper's cutoff is the first dyadic level with `2^j > 4 |S|`. -/

namespace Kr25Ssmxt

private theorem exists_cutoff (count : Nat) :
    ∃ j : Nat, 4 * count < 2 ^ j := by
  exact ⟨4 * count, (4 * count).lt_two_pow_self⟩

noncomputable def dyadicCutoff (count : Nat) : Nat :=
  Nat.find (exists_cutoff count)

theorem dyadicCutoff_spec (count : Nat) :
    4 * count < 2 ^ dyadicCutoff count :=
  Nat.find_spec (exists_cutoff count)

theorem dyadicCutoff_pos (count : Nat) (hcount : 0 < count) :
    0 < dyadicCutoff count := by
  have hspec := dyadicCutoff_spec count
  by_contra h
  have hz : dyadicCutoff count = 0 := Nat.eq_zero_of_not_pos h
  simp [hz] at hspec
  omega

theorem dyadicCutoff_previous (count : Nat)
    (hcount : 0 < count) :
    2 ^ (dyadicCutoff count - 1) ≤ 4 * count := by
  have hpos := dyadicCutoff_pos count hcount
  have hmin := Nat.find_min (exists_cutoff count)
    (Nat.sub_lt hpos (by omega : 0 < 1))
  simpa [dyadicCutoff, not_lt] using hmin

theorem dyadicCutoff_half (count : Nat)
    (hcount : 0 < count) :
    2 * count < 2 ^ (dyadicCutoff count - 1) := by
  have hpos := dyadicCutoff_pos count hcount
  have hspec := dyadicCutoff_spec count
  have hpow : 2 ^ dyadicCutoff count =
      2 * 2 ^ (dyadicCutoff count - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
    rw [pow_succ]
    omega
  rw [hpow] at hspec
  omega

theorem dyadicCutoff_mean_window
    (count : Nat) (hcount : 0 < count)
    (threshold : Real) (hthreshold : 0 ≤ threshold) :
    threshold / 4 ≤
        threshold * count / (2 : Real) ^ (dyadicCutoff count - 1) ∧
      (threshold * count / (2 : Real) ^ (dyadicCutoff count - 1) <
        threshold / 2 ∨ threshold = 0) := by
  let d : Nat := dyadicCutoff count - 1
  have hpow : (0 : Real) < (2 : Real) ^ d := by positivity
  have hprev : (2 : Real) ^ d ≤ 4 * count := by
    exact_mod_cast dyadicCutoff_previous count hcount
  have hhalf : (2 : Real) * count < (2 : Real) ^ d := by
    exact_mod_cast dyadicCutoff_half count hcount
  constructor
  · apply (div_le_div_iff₀ (by norm_num : (0 : Real) < 4) hpow).2
    nlinarith [mul_nonneg hthreshold (sub_nonneg.mpr hprev)]
  · by_cases ht : threshold = 0
    · exact Or.inr ht
    · left
      have htpos : 0 < threshold := lt_of_le_of_ne hthreshold (Ne.symm ht)
      apply (div_lt_div_iff₀ hpow (by norm_num : (0 : Real) < 2)).2
      nlinarith [mul_pos htpos (sub_pos.mpr hhalf)]

/-- Any component intensity bounded by four thirds of the total lattice
count is already below the first-loop guard at the last admissible level. -/
theorem dyadicCutoff_intensity_below
    (count : Nat) (hcount : 0 < count)
    (threshold intensity : Real) (hthreshold : 0 < threshold)
    (hintensity : intensity ≤ (4 / 3) * threshold * count) :
    intensity / (2 : Real) ^ (dyadicCutoff count - 1) <
      threshold := by
  have hhalf : (2 : Real) * count <
      (2 : Real) ^ (dyadicCutoff count - 1) := by
    exact_mod_cast dyadicCutoff_half count hcount
  have hpow : 0 < (2 : Real) ^ (dyadicCutoff count - 1) := by
    positivity
  apply (div_lt_iff₀ hpow).2
  nlinarith [mul_pos hthreshold (sub_pos.mpr hhalf)]

theorem rateExit_zero_at_cutoff
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (count : Nat) (hcount : 0 < count)
    (threshold : Real) (hthreshold : 0 < threshold)
    (hrate : (s.p : Real) =
      1 / (2 : Real) ^ (dyadicCutoff count - 1))
    (hintensity : (intensity : Real) ≤
      (4 / 3) * threshold * count) :
    ttcPseudocode.firstLoopExit s intensity threshold = 0 := by
  apply rateExit_zero_of_lt
  rw [NNReal.coe_mul, hrate, mul_one_div]
  exact dyadicCutoff_intensity_below count hcount threshold
    (intensity : Real) hthreshold hintensity

/-- The deterministic first while-loop cannot jump across the last
admissible dyadic level, even if it performs several halvings at once. -/
theorem rateExit_le_cutoff_gap
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (count : Nat) (hcount : 0 < count)
    (threshold : Real) (hthreshold : 0 < threshold)
    (level : Nat)
    (hlevel : level ≤ dyadicCutoff count - 1)
    (hrate : s.p = 1 / (2 : NNReal) ^ level)
    (hintensity : (intensity : Real) ≤
      (4 / 3) * threshold * count) :
    ttcPseudocode.firstLoopExit s intensity threshold ≤
      dyadicCutoff count - 1 - level := by
  let d := dyadicCutoff count - 1
  have hgap : level + (d - level) = d := Nat.add_sub_of_le hlevel
  have hguard :
      ((intensity * s.p / (2 : NNReal) ^ (d - level) : NNReal) : Real) <
        threshold := by
    rw [hrate]
    have hdenom : (0 : NNReal) < (2 : NNReal) ^ level := by positivity
    have hpow : (0 : NNReal) < (2 : NNReal) ^ (d - level) := by positivity
    have hform :
        intensity * (1 / (2 : NNReal) ^ level) /
          (2 : NNReal) ^ (d - level) =
          intensity / (2 : NNReal) ^ d := by
      have hpoweq : (2 : NNReal) ^ level * (2 : NNReal) ^ (d - level) =
          (2 : NNReal) ^ d := by rw [← pow_add, hgap]
      calc
        intensity * (1 / (2 : NNReal) ^ level) /
            (2 : NNReal) ^ (d - level) =
            intensity / ((2 : NNReal) ^ level * (2 : NNReal) ^ (d - level)) := by
              simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
              ac_rfl
        _ = intensity / (2 : NNReal) ^ d := by rw [hpoweq]
    rw [hform]
    simpa only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using
      dyadicCutoff_intensity_below count hcount threshold
        (intensity : Real) hthreshold hintensity
  unfold ttcPseudocode.firstLoopExit
  exact Nat.sInf_le hguard

end Kr25Ssmxt
