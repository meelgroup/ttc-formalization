/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# The volume-estimation problem

The formula is `F = (M, φ)`: an interpretation `M` sending each atom index to the set it
denotes, and a Boolean combination `Ttc.BForm A` of those indices.  The quantity to
estimate is `Vol(F)`, the Lebesgue volume of `Sol(F) ⊆ ℝⁿ`; `TTC` returns a value within
`(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`.

Two definitions and nothing else — **what** the algorithm estimates and **how accurately**
it is asked to estimate it.  They are the only two symbols a reader must accept before
reading `Model/Theorem`.

The volume is taken at the **user's own** `φ`, not at the preprocessed formula the
algorithm runs on; that the preprocessing moves neither `Sol(F)` nor its volume is *proof*
content, and it is what lets the headline avoid a surrogate.

**No assumption is stated here.**  `Ttc.VolSolCheck.volSol_eq_lra` checks `volSol` against
an independent `Bool`-valued evaluator and `…measurableSet_sol_lra` shows the set is
measurable; both live in `Volume/VolSolCheck.lean`, which imports this file.
-/

namespace Ttc

/-- **The paper's `Vol(F)`**: the Lebesgue volume of the solution set. -/
noncomputable def volSol {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A) : ℝ :=
  (MeasureTheory.volume (sol M φ)).toReal

/-- **The relative-error interval** `(1 ± ε)·b = [(1−ε)b, (1+ε)b]`.  `@[reducible]` so
it is definitionally transparent to `Set.Icc`. -/
@[reducible] def relErr (ε b : ℝ) : Set ℝ := Set.Icc ((1 - ε) * b) ((1 + ε) * b)

end Ttc
