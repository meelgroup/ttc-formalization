import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Model.Program

/-!
# Scalar parameter envelope for lattice-count accuracy

This file separates the elementary nonlinear inequalities which turn the paper's
component-volume, lattice-comparison, and sampling errors into the final `epsilon / 2`
relative-error allowance.
-/

noncomputable section

namespace Kr25Ssmxt

/-- The three `ε'` factors and one lattice-comparison factor used in the
component-prefix invariant lie inside the final `epsilon / 2` envelope.

INTERNAL: scalar arithmetic in the assembly of `process_components_lattice_count_accuracy`.
-/
lemma process_components_lattice_count_accuracy_parameter_envelope
    (params : ApproxParams) :
    1 - params.epsilon / 2 ≤
        (1 - params.ε') ^ 3 * (1 - params.latticeEta) ∧
      (1 + params.ε') ^ 3 * (1 + params.latticeEta) ≤
        1 + params.epsilon / 2 := by
  dsimp only [ApproxParams.ε', ApproxParams.latticeEta]
  have he0 : 0 ≤ params.epsilon := le_of_lt params.epsilon_pos
  have he2 : params.epsilon ^ 2 ≤ params.epsilon := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr params.epsilon_le_one)]
  have he3 : params.epsilon ^ 3 ≤ params.epsilon ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg params.epsilon)
      (sub_nonneg.mpr params.epsilon_le_one)]
  have he3_nonneg : 0 ≤ params.epsilon ^ 3 := pow_nonneg he0 3
  constructor
  · have hbracket :
        0 ≤ 1728 + 720 * params.epsilon - 44 * params.epsilon ^ 2 +
          params.epsilon ^ 3 := by
      nlinarith
    have hscaled := mul_nonneg he0 hbracket
    nlinarith
  · have hbracket :
        0 ≤ 1728 - 720 * params.epsilon - 44 * params.epsilon ^ 2 -
          params.epsilon ^ 3 := by
      nlinarith [params.epsilon_le_one]
    have hscaled := mul_nonneg he0 hbracket
    nlinarith

end Kr25Ssmxt
