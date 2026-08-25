import Kr25Ssmxt.Model.Pseudocode
import Kr25Ssmxt.Analysis.PoissonTwoSidedTailPade

/-!
# Poisson concentration in the threshold-sized regime

This is the analytic concentration input for the component-fold argument.  Its explicit
lower bound on the mean is essential: the low-intensity case is not covered by the paper's
threshold calculation.
-/

noncomputable section

open scoped NNReal ProbabilityTheory
open ProbabilityTheory

namespace Kr25Ssmxt

/-- A Poisson variable has relative error at most `epsilon` except with probability `delta`
once its mean is large enough for the standard two-sided Chernoff estimate.

INTERNAL: per-level concentration in the adaptive dyadic split for
`process_components_lattice_count_accuracy`.
-/
lemma process_components_lattice_count_accuracy_poisson_concentration
    (mean : NNReal) (epsilon delta : Real)
    (hepsilon : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hmean : 3 * Real.log (2 / delta) / epsilon ^ 2 ≤ (mean : Real)) :
    (poissonMeasure mean).real
        {count | (count : Real) ∈ Arlib.relErr epsilon (mean : Real)} ≥
      1 - delta := by
  let mu : Real := mean
  have hquot : 0 < 2 / delta := div_pos (by norm_num) hdelta
  have hquot_one : 1 < 2 / delta := by
    apply (lt_div_iff₀ hdelta).2
    linarith
  have hlog : 0 < Real.log (2 / delta) := Real.log_pos hquot_one
  have hepsilon_sq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hmu : 0 < mu := by
    have hleft : 0 < 3 * Real.log (2 / delta) / epsilon ^ 2 := by positivity
    exact lt_of_lt_of_le hleft hmean
  let a := epsilon * mu
  have ha : 0 < a := mul_pos hepsilon hmu
  have hamu : a ≤ mu := by
    dsimp [a]
    nlinarith
  have htail := poisson_two_sided_tail_pade hmu ha hamu
  have hden : 0 < 2 + epsilon := by linarith
  have hratio : a ^ 2 / (2 * mu + a) = epsilon ^ 2 * mu / (2 + epsilon) := by
    dsimp [a]
    field_simp
    ring
  have hfrac : epsilon ^ 2 * mu / 3 ≤ epsilon ^ 2 * mu / (2 + epsilon) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : Real) < 3) hden]
    have hnonneg : 0 ≤ epsilon ^ 2 * mu := by positivity
    nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hepsilon_le_one)]
  have htail' :
      ∑' k : Nat,
          (if a ≤ |(k : Real) - mu| then Arlib.Probability.poissonPMF mu k else 0) ≤
        2 * Real.exp (-(epsilon ^ 2 * mu / 3)) := by
    refine htail.trans ?_
    rw [hratio]
    gcongr
    linarith
  have hlog_le : Real.log (2 / delta) ≤ epsilon ^ 2 * mu / 3 := by
    have h := (div_le_iff₀ hepsilon_sq).mp hmean
    dsimp [mu] at h ⊢
    nlinarith
  have hexp_bound : 2 * Real.exp (-(epsilon ^ 2 * mu / 3)) ≤ delta := by
    calc
      2 * Real.exp (-(epsilon ^ 2 * mu / 3))
          ≤ 2 * Real.exp (-Real.log (2 / delta)) := by
            gcongr
            linarith
      _ = delta := by
        rw [Real.exp_neg, Real.exp_log hquot]
        field_simp
  let bad : Set Nat := {k | a ≤ |(k : Real) - mu|}
  have hbad_measure :
      (poissonMeasure mean).real bad =
        ∑' k : Nat,
          (if a ≤ |(k : Real) - mu| then Arlib.Probability.poissonPMF mu k else 0) := by
    rw [← MeasureTheory.integral_indicator_one (MeasurableSet.of_discrete bad)]
    rw [ProbabilityTheory.integral_poissonMeasure]
    apply tsum_congr
    intro k
    by_cases hk : a ≤ |(k : Real) - mu|
    · simp [bad, hk, Arlib.Probability.poissonPMF, mu]
    · simp [bad, hk]
  have hbad : (poissonMeasure mean).real bad ≤ delta := by
    rw [hbad_measure]
    exact htail'.trans hexp_bound
  let good : Set Nat :=
    {k | (k : Real) ∈ Arlib.relErr epsilon mu}
  have hsubset : goodᶜ ⊆ bad := by
    intro k hk
    change a ≤ |(k : Real) - mu|
    change ¬ ((1 - epsilon) * mu ≤ (k : Real) ∧
      (k : Real) ≤ (1 + epsilon) * mu) at hk
    by_cases hlower : (1 - epsilon) * mu ≤ (k : Real)
    · have hupper : (1 + epsilon) * mu < (k : Real) :=
        lt_of_not_ge (fun h ⇒ hk ⟨hlower, h⟩)
      rw [abs_of_nonneg (by linarith : 0 ≤ (k : Real) - mu)]
      dsimp [a]
      nlinarith
    · have hbelow : (k : Real) < (1 - epsilon) * mu := lt_of_not_ge hlower
      rw [abs_of_nonpos (by linarith : (k : Real) - mu ≤ 0)]
      dsimp [a]
      nlinarith
  have hcompl : (poissonMeasure mean).real goodᶜ ≤ delta :=
    (MeasureTheory.measureReal_mono hsubset).trans hbad
  have hcompl_eq :
      (poissonMeasure mean).real goodᶜ = 1 - (poissonMeasure mean).real good := by
    rw [MeasureTheory.measureReal_compl (MeasurableSet.of_discrete good),
      ProbabilityTheory.probReal_univ]
  change (poissonMeasure mean).real good ≥ 1 - delta
  rw [hcompl_eq] at hcompl
  linarith

end Kr25Ssmxt
