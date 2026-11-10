import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.ManuscriptDyadicChernoffSum
import Kr25Ssmxt.Analysis.ManuscriptDyadicCutoff

/-! A uniform lower bound on the Poisson mean at each dyadic level before
the manuscript cutoff. -/

namespace Kr25Ssmxt

theorem ApproxParams.lower_intensity_factor
    (p : ApproxParams) :
    (1 - p.ε') * (1 - p.latticeEta) ≥ 1 / 2 := by
  dsimp [ApproxParams.ε', ApproxParams.latticeEta]
  have he : 0 ≤ p.epsilon := p.epsilon_pos.le
  have he2 : p.epsilon ^ 2 ≤ p.epsilon := by
    nlinarith [mul_nonneg he (sub_nonneg.mpr p.epsilon_le_one)]
  nlinarith [p.epsilon_le_one]

theorem manuscript_dyadic_mean_lower
    (p : ApproxParams) (m count : Nat) (hcount : 0 < count)
    (level : Nat)
    (hlevel : level ≤ manuscriptDyadicCutoff count - 1) :
    ((count : Real) * p.Thresh m *
      (1 - p.ε') ^ 2 * (1 - p.latticeEta)) /
        (2 : Real) ^ level ≥
      (1 - p.ε') * p.Thresh m / 8 *
        (2 : Real) ^ (manuscriptDyadicCutoff count - 1 - level) := by
  let d := manuscriptDyadicCutoff count - 1
  have hpowLevel : 0 < (2 : Real) ^ level := by positivity
  have hpowGap : 0 < (2 : Real) ^ (d - level) := by positivity
  have hpoweq : (2 : Real) ^ level * (2 : Real) ^ (d - level) =
      (2 : Real) ^ d := by
    rw [← pow_add, Nat.add_sub_of_le hlevel]
  have hprevious : (2 : Real) ^ d ≤ 4 * count := by
    exact_mod_cast manuscriptDyadicCutoff_previous count hcount
  have hcountRate :
      ((count : Real) / (2 : Real) ^ level) ≥
        (2 : Real) ^ (d - level) / 4 := by
    apply (div_le_div_iff₀ (by norm_num : (0 : Real) < 4) hpowLevel).2
    nlinarith [hpoweq, hprevious]
  have hfactor : (1 - p.ε') / 2 ≤
      (1 - p.ε') ^ 2 * (1 - p.latticeEta) := by
    have hnonneg : 0 ≤ 1 - p.ε' := by
      dsimp [ApproxParams.ε']
      linarith [p.epsilon_le_one]
    have h := mul_le_mul_of_nonneg_left (p.lower_intensity_factor)
      hnonneg
    nlinarith
  have hscale : 0 ≤ (1 - p.ε') ^ 2 *
      (1 - p.latticeEta) * p.Thresh m := by
    have hnonneg : 0 ≤ 1 - p.latticeEta := by
      dsimp [ApproxParams.latticeEta]
      linarith [p.epsilon_le_one]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hnonneg)
      (p.threshold_pos m).le
  have hmean1 := mul_le_mul_of_nonneg_right hcountRate hscale
  have hmean2 := mul_le_mul_of_nonneg_right hfactor
    (mul_nonneg (p.threshold_pos m).le hpowGap.le)
  apply (le_div_iff₀ hpowLevel).2
  nlinarith [hmean1, hmean2]

end Kr25Ssmxt
