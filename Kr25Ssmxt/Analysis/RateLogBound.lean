import Kr25Ssmxt.Analysis.RuntimeBudgets
import Kr25Ssmxt.Analysis.ManuscriptThinningCosts
import Kr25Ssmxt.Model.Run

/-! Elementary logarithmic bounds used to remove the decimal scale from
the first thinning loop's operation count. -/

namespace Kr25Ssmxt

theorem ceil_decimal_mul_le (k : Nat) (u : Real) :
    Nat.ceil ((10 : Real) ^ k * u) + 1 ≤
      10 ^ k * (Nat.ceil u + 1) := by
  have hm : (10 : Real) ^ k * u ≤
      ((10 ^ k * Nat.ceil u : Nat) : Real) := by
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil u) (by positivity)
  have hc := Nat.ceil_mono hm
  rw [Nat.ceil_natCast] at hc
  have hpow : 1 ≤ (10 : Nat) ^ k := by
    have hp : 0 < (10 : Nat) ^ k := by positivity
    omega
  simp only [mul_add, mul_one]
  omega

theorem clog_two_mul_le (a b : Nat) :
    Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by omega) a)
    (Nat.le_pow_clog (by omega) b)

theorem clog_two_ten_pow_le (k : Nat) :
    Nat.clog 2 (10 ^ k) ≤ 4 * k := by
  apply Nat.clog_le_of_le_pow
  calc
    10 ^ k ≤ 16 ^ k := Nat.pow_le_pow_left (show (10 : Nat) ≤ 16 by omega) k
    _ = 2 ^ (4 * k) := by rw [show (16 : Nat) = 2 ^ 4 by norm_num, pow_mul]

theorem clog_two_decimal_scaled_le (k a : Nat) :
    Nat.clog 2 (10 ^ k * a) ≤ 4 * k + Nat.clog 2 a := by
  exact (clog_two_mul_le _ _).trans (Nat.add_le_add_right
    (clog_two_ten_pow_le k) _)

theorem clog_two_pow_le (a n : Nat) :
    Nat.clog 2 (a ^ n) ≤ n * Nat.clog 2 a := by
  apply Nat.clog_le_of_le_pow
  rw [mul_comm n, pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by omega) a) n

theorem clog_two_ceil_two_pow_le (u : Real) (n : Nat) (hu : 0 ≤ u) :
    Nat.clog 2 (Nat.ceil (2 * u ^ n) + 1) ≤
      2 + n * Nat.clog 2 (Nat.ceil u + 1) := by
  let a := Nat.ceil u + 1
  have hua : u ≤ (a : Real) := by
    dsimp [a]
    exact (Nat.le_ceil u).trans (by exact_mod_cast Nat.le_succ _)
  have hpow : 2 * u ^ n ≤ ((2 * a ^ n : Nat) : Real) := by
    push_cast
    gcongr
  have hceil := Nat.ceil_mono hpow
  rw [Nat.ceil_natCast] at hceil
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hapow : 1 ≤ a ^ n := one_le_pow₀ ha
  have hnat : Nat.ceil (2 * u ^ n) + 1 ≤ 4 * a ^ n := by omega
  calc
    Nat.clog 2 (Nat.ceil (2 * u ^ n) + 1) ≤ Nat.clog 2 (4 * a ^ n) :=
      Nat.clog_mono_right 2 hnat
    _ ≤ Nat.clog 2 4 + Nat.clog 2 (a ^ n) := clog_two_mul_le _ _
    _ ≤ 2 + n * Nat.clog 2 a := by
      simpa [show Nat.clog 2 4 = 2 by decide] using
        Nat.add_le_add_left (clog_two_pow_le a n) 2

theorem clog_two_ceil_decimal_mul_le (k : Nat) (u : Real) :
    Nat.clog 2 (Nat.ceil ((10 : Real) ^ k * u) + 1) ≤
      4 * k + Nat.clog 2 (Nat.ceil u + 1) := by
  calc
    Nat.clog 2 (Nat.ceil ((10 : Real) ^ k * u) + 1) ≤
        Nat.clog 2 (10 ^ k * (Nat.ceil u + 1)) :=
      Nat.clog_mono_right 2 (ceil_decimal_mul_le k u)
    _ ≤ 4 * k + Nat.clog 2 (Nat.ceil u + 1) :=
      clog_two_decimal_scaled_le _ _

theorem manuscript_intensity_div_threshold (b n : Nat)
    {threshold : Real} (hthreshold : 0 < threshold) (volume : NNReal) :
    ((ttcPseudocode.t b n threshold volume : NNReal) : Real) / threshold =
      (10 : Real) ^ (b * n) * (volume : Real) := by
  unfold ttcPseudocode.t
  push_cast
  rw [Real.coe_toNNReal _ hthreshold.le]
  field_simp

theorem manuscript_rate_clog_le_linear_precision (b n : Nat)
    {threshold : Real} (hthreshold : 0 < threshold) (volume : NNReal) :
    Nat.clog 2
        (Nat.ceil (((ttcPseudocode.t b n threshold volume : NNReal) : Real) /
          threshold) + 1) ≤
      4 * (b * n) + Nat.clog 2 (Nat.ceil (volume : Real) + 1) := by
  rw [manuscript_intensity_div_threshold b n hthreshold volume]
  exact clog_two_ceil_decimal_mul_le (b * n) (volume : Real)

theorem clipped_component_rate_clog_le_linear_precision {n : Nat}
    (P : PolytopeData n) (p : ApproxParams) (m b : Nat) :
    let v := max (P.volumeClipLower p.ε')
      (P.volumeClipUpper p.ε')
    Nat.clog 2
        (Nat.ceil (((ttcPseudocode.t b n (p.Thresh m) v : NNReal) : Real) /
          p.Thresh m) + 1) ≤
      4 * (b * n) + Nat.clog 2 (Nat.ceil (v : Real) + 1) := by
  exact manuscript_rate_clog_le_linear_precision b n
    (p.threshold_pos m) _

theorem TTCRuntime.manuscriptExpectedComponentBudget_le_linearPrecision
    {n : Nat} (hn : 21 ≤ n) (p : ApproxParams)
    (m b cv18NonQueryFactor : Nat) (P : PolytopeData n) :
    TTCRuntime.manuscriptExpectedComponentBudget hn p m b cv18NonQueryFactor P ≤
      TTCRuntime.manuscriptExpectedComponentBudgetLinearPrecision hn p m b
        cv18NonQueryFactor P := by
  unfold TTCRuntime.manuscriptExpectedComponentBudget
    TTCRuntime.manuscriptExpectedComponentBudgetLinearPrecision
  dsimp only
  gcongr
  exact_mod_cast clipped_component_rate_clog_le_linear_precision P p m b

end Kr25Ssmxt
