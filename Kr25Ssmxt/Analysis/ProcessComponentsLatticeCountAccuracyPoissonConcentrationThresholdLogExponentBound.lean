import Kr25Ssmxt.Model.Program

/-!
# Rearranging the Poisson concentration threshold

This file isolates the ordered-field calculation which turns the prescribed lower bound
on a Poisson mean into the exponent comparison used by the Chernoff estimate.
-/

noncomputable section

open scoped NNReal

namespace Kr25Ssmxt

/-- The threshold lower bound implies that the Chernoff exponent is no larger than the
negative logarithm of the target failure ratio.

INTERNAL: scalar rearrangement in
`process_components_lattice_count_accuracy_poisson_concentration_threshold_exponential_bound`.
-/
lemma process_components_lattice_count_accuracy_poisson_concentration_threshold_log_exponent_bound
    (mean : NNReal) (epsilon delta : Real)
    (hepsilon : 0 < epsilon)
    (hmean : 3 * Real.log (2 / delta) / epsilon ^ 2 ≤ (mean : Real)) :
    - (mean : Real) * epsilon ^ 2 / 3 ≤ -Real.log (2 / delta) := by
  have heps_sq : 0 < epsilon ^ 2 := by
    positivity
  have hscaled := (div_le_iff₀ heps_sq).mp hmean
  nlinarith [hscaled]

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · cleared the positive `epsilon ^ 2` denominator and normalized
  the resulting scalar inequality
-/

end Kr25Ssmxt
