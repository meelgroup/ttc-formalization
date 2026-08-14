import Ttc.Exec.CVGaussianWarmFallbackZeroSafeOperational

/-! Error shares for `k` independent Gaussian cooling streams. -/

namespace Ttc.CVGaussianBlockRetryParameters

open MeasureTheory ProbabilityTheory Set Arlib
open Ttc.CVCorrected Ttc.CVAdaptive Ttc.CVContinuingRetryParameters
open scoped ENNReal

noncomputable def blockShare (m k : Nat) (eps : Real) : Real :=
  correctedNu m eps / (8 * ((k : Real) + 1))

noncomputable def blockZeta (m k : Nat) (eps : Real) : ENNReal :=
  ENNReal.ofReal (correctedNu m eps / (256 * ((k : Real) + 1)))

noncomputable def blockEta (m k : Nat) (eps : Real) : ENNReal :=
  ENNReal.ofReal (blockShare m k eps)

noncomputable def blockRetries (m k : Nat) (eps : Real) : Nat :=
  16 * explicitDyadicTailIndex (blockShare m k eps)

noncomputable def blockMixError (m k : Nat) (eps : Real) : ENNReal :=
  32 * blockZeta m k eps +
    (blockEta m k eps + continuingContraction ^ blockRetries m k eps)

theorem blockShare_pos {m k : Nat} {eps : Real} (heps : 0 < eps) :
    0 < blockShare m k eps := by
  unfold blockShare
  exact div_pos (correctedNu_pos heps) (by positivity)

theorem blockShare_lt_one {m k : Nat} {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) : blockShare m k eps < 1 := by
  have hnu := correctedNu_le_one (m := m) heps heps1
  unfold blockShare
  have hk : (1 : Real) ≤ (k : Real) + 1 := by
    have := (Nat.cast_nonneg k : (0 : Real) ≤ (k : Real))
    linarith
  have hd : (8 : Real) ≤ 8 * ((k : Real) + 1) := by nlinarith
  have hden : 0 < 8 * ((k : Real) + 1) := by positivity
  rw [div_lt_one hden]
  linarith

theorem contraction_pow_blockRetries_le_share
    {m k : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (15 / 16 : Real) ^ blockRetries m k eps ≤ blockShare m k eps := by
  let j := explicitDyadicTailIndex (blockShare m k eps)
  have hpow : ((15 / 16 : Real) ^ 16) ^ j ≤ ((1 / 2 : Real)) ^ j :=
    pow_le_pow_left₀ (by positivity) contraction_pow_sixteen_le_half j
  have hdyadic : (1 / 2 : Real) ^ j ≤ blockShare m k eps := by
    simpa only [one_div, inv_pow] using
      (inv_two_pow_explicitDyadicTailIndex_le
        (blockShare_pos (m := m) (k := k) heps) (blockShare_lt_one heps heps1))
  rw [blockRetries, pow_mul]
  exact hpow.trans hdyadic

theorem continuingContraction_pow_blockRetries_le_eta
    {m k : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    continuingContraction ^ blockRetries m k eps ≤ blockEta m k eps := by
  rw [continuingContraction, blockEta, ← ENNReal.ofReal_pow]
  exact ENNReal.ofReal_le_ofReal (contraction_pow_blockRetries_le_share heps heps1)
  norm_num

theorem blockZeta_le_sixteenth
    {m k : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    blockZeta m k eps ≤ ENNReal.ofReal (1 / 16 : Real) := by
  apply ENNReal.ofReal_le_ofReal
  have hnu := correctedNu_le_one (m := m) heps heps1
  have hk : (1 : Real) ≤ (k : Real) + 1 := by
    have := (Nat.cast_nonneg k : (0 : Real) ≤ (k : Real))
    linarith
  have hd : (256 : Real) ≤ 256 * ((k : Real) + 1) := by nlinarith
  have hden : 0 < 256 * ((k : Real) + 1) := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

theorem blockMixError_ne_top (m k : Nat) (eps : Real) :
    blockMixError m k eps ≠ ⊤ := by
  unfold blockMixError blockZeta blockEta blockShare continuingContraction
  finiteness

/-- Tensorized dependence budget: the scalar phase error is divided by `k+1`. -/
theorem blockMixError_budget {m k : Nat} {eps : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (k : Real) * (2 * (blockMixError m k eps).toReal) ≤ correctedNu m eps := by
  have htail := continuingContraction_pow_blockRetries_le_eta
    (m := m) (k := k) heps heps1
  have hnu0 : 0 ≤ correctedNu m eps := (correctedNu_pos heps).le
  have hshare0 : 0 ≤ blockShare m k eps := (blockShare_pos heps).le
  have hzeta0 : 0 ≤ correctedNu m eps / (256 * ((k : Real) + 1)) := by positivity
  have htailTop : continuingContraction ^ blockRetries m k eps ≠ ⊤ := by
    unfold continuingContraction
    finiteness
  have hetaTop : blockEta m k eps ≠ ⊤ := ENNReal.ofReal_ne_top
  have hzetaTop : blockZeta m k eps ≠ ⊤ := ENNReal.ofReal_ne_top
  have htailReal : (continuingContraction ^ blockRetries m k eps).toReal ≤
      blockShare m k eps := by
    simpa only [blockEta, ENNReal.toReal_ofReal hshare0] using
      ((ENNReal.toReal_le_toReal htailTop hetaTop).2 htail)
  rw [blockMixError,
    ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) hzetaTop)
      (ENNReal.add_ne_top.2 ⟨hetaTop, htailTop⟩),
    ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_add hetaTop htailTop,
    blockZeta, ENNReal.toReal_ofReal hzeta0,
    blockEta, ENNReal.toReal_ofReal hshare0]
  unfold blockShare
  have hd : 0 < (k : Real) + 1 := by positivity
  have hfrac : (k : Real) / ((k : Real) + 1) ≤ 1 := by
    rw [div_le_one hd]
    linarith
  calc
    (k : Real) *
        (2 * (32 * (correctedNu m eps / (256 * ((k : Real) + 1))) +
          (correctedNu m eps / (8 * ((k : Real) + 1)) +
            (continuingContraction ^ blockRetries m k eps).toReal))) ≤
      (k : Real) *
        (2 * (32 * (correctedNu m eps / (256 * ((k : Real) + 1))) +
          (correctedNu m eps / (8 * ((k : Real) + 1)) +
            correctedNu m eps / (8 * ((k : Real) + 1))))) := by
      gcongr
      simpa only [blockShare] using htailReal
    _ = (3 / 4 : Real) * ((k : Real) / ((k : Real) + 1)) *
        correctedNu m eps := by field_simp; ring
    _ ≤ correctedNu m eps := by
      have hk0 : 0 ≤ (k : Real) / ((k : Real) + 1) := by positivity
      nlinarith

theorem blockMixError_scalar_budget {m k : Nat} {eps : Real}
    (hk : 0 < k) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    2 * (blockMixError m k eps).toReal ≤ correctedNu m eps := by
  have hblock := blockMixError_budget (m := m) (k := k) heps heps1
  have hkR : (1 : Real) ≤ k := by exact_mod_cast hk
  have he0 : 0 ≤ 2 * (blockMixError m k eps).toReal := by positivity
  exact (le_mul_of_one_le_left he0 hkR).trans hblock

#print axioms blockMixError_budget
#print axioms continuingContraction_pow_blockRetries_le_eta
#print axioms blockMixError_scalar_budget

end Ttc.CVGaussianBlockRetryParameters
