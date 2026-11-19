import ttc.Analysis.PoissonMeasureRealEqTsumIndicator
import ttc.Analysis.PoissonMultiplicativeTwoSidedTsum

/-!
# A two-sided Chernoff bound for the Poisson relative-error event

This isolates the distributional input to
`process_components_lattice_count_accuracy_poisson_concentration`.  Its conclusion is
stated directly using the relative-error event needed by that theorem.
-/

noncomputable section

open scoped NNReal ProbabilityTheory
open ProbabilityTheory

namespace ttc

/-- The probability that a Poisson variable misses its closed relative-error interval is
bounded by the standard two-sided Chernoff estimate.

PAPER: sections/analysis.tex:240-242
-/
lemma process_components_lattice_count_accuracy_poisson_concentration_chernoff_failure_bound
    (mean : NNReal) (epsilon : Real)
    (hepsilon : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1) :
    (poissonMeasure mean).real
        {count | ¬ ((count : Real) ∈ Arlib.relErr epsilon (mean : Real))} ≤
      2 * Real.exp (- (mean : Real) * epsilon ^ 2 / 3) := by
  by_cases hmean : mean = 0
  · subst mean
    calc
      (poissonMeasure 0).real
          {count | ¬ ((count : Real) ∈ Arlib.relErr epsilon (0 : Real))} ≤ 1 :=
        MeasureTheory.measureReal_le_one
      _ ≤ 2 * Real.exp (- (0 : Real) * epsilon ^ 2 / 3) := by norm_num
  · have hmu : 0 < (mean : Real) := by
      exact_mod_cast (pos_of_ne_zero hmean)
    have hsubset :
        {count : Nat | ¬ ((count : Real) ∈ Arlib.relErr epsilon (mean : Real))} ⊆
          {count : Nat | epsilon * (mean : Real) ≤ |(count : Real) - (mean : Real)|} := by
      intro count hbad
      by_contra hdev
      apply hbad
      have habs : |(count : Real) - (mean : Real)| < epsilon * (mean : Real) :=
        lt_of_not_ge hdev
      rw [abs_lt] at habs
      change (1 - epsilon) * (mean : Real) ≤ (count : Real) ∧
        (count : Real) ≤ (1 + epsilon) * (mean : Real)
      constructor <;> linarith
    calc
      (poissonMeasure mean).real
          {count | ¬ ((count : Real) ∈ Arlib.relErr epsilon (mean : Real))} ≤
          (poissonMeasure mean).real
            {count | epsilon * (mean : Real) ≤ |(count : Real) - (mean : Real)|} :=
        MeasureTheory.measureReal_mono hsubset
      _ = ∑' count : Nat, if epsilon * (mean : Real) ≤
            |(count : Real) - (mean : Real)| then
            Arlib.Probability.poissonPMF (mean : Real) count else 0 :=
        poissonMeasure_real_eq_tsum_indicator mean _
      _ ≤ 2 * Real.exp (- (mean : Real) * epsilon ^ 2 / 3) :=
        poisson_multiplicative_two_sided_tsum (mean : Real) epsilon hmu hepsilon
          hepsilon_le_one

end ttc
