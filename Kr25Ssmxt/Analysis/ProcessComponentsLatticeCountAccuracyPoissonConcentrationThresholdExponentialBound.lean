import Kr25Ssmxt.Analysis.PreludeProof

/-!
# The scalar threshold calculation for Poisson concentration

This separates the real-arithmetic part of
`process_components_lattice_count_accuracy_poisson_concentration` from its probabilistic
Chernoff argument.
-/

noncomputable section

open scoped NNReal

namespace Kr25Ssmxt

/-- The paper's lower bound on the Poisson mean makes the two-sided Chernoff error at most
`delta`.

PAPER: main-arxiv.tex:1181-1187
-/
lemma process_components_lattice_count_accuracy_poisson_concentration_threshold_exponential_bound
    (mean : NNReal) (epsilon delta : Real)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hmean : 3 * Real.log (2 / delta) / epsilon ^ 2 ≤ (mean : Real)) :
    2 * Real.exp (- (mean : Real) * epsilon ^ 2 / 3) ≤ delta := by
  have heps2 : 0 < epsilon ^ 2 := by positivity
  have hscaled : 3 * Real.log (2 / delta) ≤ (mean : Real) * epsilon ^ 2 :=
    (div_le_iff₀ heps2).mp hmean
  have hlog : Real.log (2 / delta) ≤ (mean : Real) * epsilon ^ 2 / 3 := by
    apply (le_div_iff₀ (by norm_num : (0 : Real) < 3)).2
    simpa [mul_comm] using hscaled
  have hneg : - (mean : Real) * epsilon ^ 2 / 3 ≤ -Real.log (2 / delta) := by
    calc
      - (mean : Real) * epsilon ^ 2 / 3 = -((mean : Real) * epsilon ^ 2 / 3) := by ring
      _ ≤ -Real.log (2 / delta) := neg_le_neg hlog
  have hquot : 0 < 2 / delta := by positivity
  have hexp : Real.exp (- (mean : Real) * epsilon ^ 2 / 3) ≤
      Real.exp (-Real.log (2 / delta)) := Real.exp_le_exp.mpr hneg
  calc
    2 * Real.exp (- (mean : Real) * epsilon ^ 2 / 3) ≤
        2 * Real.exp (-Real.log (2 / delta)) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = delta := by
      rw [Real.exp_neg, Real.exp_log hquot]
      rw [inv_div]
      ring

end Kr25Ssmxt
