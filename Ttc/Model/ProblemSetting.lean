/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# `Model/ProblemSetting`: the problem `alg:ttc` solves

Two definitions, and nothing else: **what** the algorithm estimates, and **how
accurately** it is asked to estimate it. Together they are the paper's problem
statement, and they are the only two symbols a reader has to accept before
reading `Model/Theorem`.

* `Ttc.volSol M φ` is the paper's `Vol(F)` — the Lebesgue volume of `Sol(F)`.
* `Ttc.relErr ε b` is the paper's `(1 ± ε)·b` interval.

**No assumption is stated here.** The hypothesis bundle the result quantifies
over is `Ttc.TtcProb` (`Ttc/TtcProb.lean`), which is an abstract interface —
`CLAUDE.md` §1's layer 1 — and not part of the problem. The two *other papers'*
assumption bundles it names are `Ttc.VolumeAlgorithm` (`Volume/Oracle`) and
`Ttc.KV97Sampler` (`Sampler/Interface`).

**Is `volSol` the volume of the right set?** That question is answered, for this
one symbol and without reference to the rest of the development, in
`Ttc/Volume/VolSolCheck.lean`: `Ttc.VolSolCheck.volSol_eq_lra` re-derives
`volSol` for an LRA formula from a `Bool`-valued evaluator, and
`Ttc.VolSolCheck.measurableSet_sol_lra` shows the set is measurable so that
`volume` is not silently an outer measure of a pathological set. The statement is
not restated here because that module imports this one; the proofs, and the
statements, live there.
-/

namespace Ttc

/-! ## What is estimated, and how accurately -/

/-- The paper's `Vol(F)`: the Lebesgue volume of the solution set. -/
noncomputable def volSol {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A) : ℝ :=
  (MeasureTheory.volume (sol M φ)).toReal

/-- The paper's `(1 ± ε)·b` interval. `@[reducible]` so it is transparent to
`Set.Icc`. -/
@[reducible] def relErr (ε b : ℝ) : Set ℝ := Set.Icc ((1 - ε) * b) ((1 + ε) * b)

end Ttc
