import Kr25Ssmxt.Model.Pseudocode
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A low-intensity obstruction to relative Poisson concentration

The paper's lattice-count proof applies a threshold-sized concentration estimate even
when its splitting index `j*` is zero.  At unit intensity this cannot hold: relative
error `1/2` around one requires the Poisson count to equal one, whose probability is
`exp (-1) < 1/2`.
-/

noncomputable section

open scoped NNReal ProbabilityTheory
open ProbabilityTheory

namespace Kr25Ssmxt

/-- A unit-rate Poisson count is not within relative error `1/2` of its mean with
probability at least `1/2`.

INTERNAL: Counterexample to using the paper's threshold concentration bound when `j* = 0`.
-/
lemma poisson_unit_not_half_accurate :
    ¬ (poissonMeasure 1).real
        {count | (count : Real) ∈ Arlib.relErr (1 / 2) 1} ≥ 1 / 2 := by
  have hevent :
      {count : Nat | (count : Real) ∈ Arlib.relErr (1 / 2) 1} = {1} := by
    ext count
    simp only [Arlib.mem_relErr, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hlower, hupper⟩
      norm_num at hlower hupper
      have hpos : 0 < count := by
        exact_mod_cast (show (0 : Real) < count by linarith)
      have hlt : count < 2 := by
        exact_mod_cast (show (count : Real) < 2 by linarith)
      omega
    · rintro rfl
      norm_num
  rw [hevent, poissonMeasure_real_singleton]
  norm_num
  exact Real.exp_neg_one_lt_half

end Kr25Ssmxt
