/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# The volume-estimation problem

The formula is `F = (M, φ)`: an interpretation `M` sending each atom index to the
set it denotes — for `TTC` a `Ttc.LinAtom`'s closed half-space — and a Boolean
combination `Ttc.BForm A` of those indices. The quantity to estimate is `Vol(F)`,
the Lebesgue volume of the solution set `Sol(F) ⊆ ℝⁿ`; `TTC` returns a value
within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`.

Two definitions, and nothing else: **what** the algorithm estimates, and **how
accurately** it is asked to estimate it. They are the only two symbols a reader
has to accept before reading `Model/Theorem`.

* `Ttc.volSol M φ` is the paper's `Vol(F)` — the Lebesgue volume of
  `Ttc.sol M φ` (`Model/Prelude`).
* `Ttc.relErr ε b` is the paper's `(1 ± ε)·b` interval.

The volume is taken at the **user's own** `φ`. The algorithm does not run on `φ`
itself but on the preprocessed formula of `Model/Pseudocode`'s lines A1–A11; that
the preprocessing moves neither `Sol(F)` nor its volume is *proof* content, and it
is what lets `Model/Theorem` state the guarantee against this file's `volSol` of
the original formula rather than against a surrogate.

`Ttc.VolSolCheck.volSol_eq_lra` checks `volSol` against an independent
`Bool`-valued evaluator, re-deriving it for an LRA formula from nothing but
`∑ i, coeff i * x i ≤ bound`, `Bool` connectives and `MeasureTheory.volume`, and
`Ttc.VolSolCheck.measurableSet_sol_lra` shows the set is measurable so that
`volume` is not silently an outer measure of a pathological set. Their proofs —
and their statements — are in `Volume/VolSolCheck.lean`, which imports this file;
**this file has none.**

**No assumption is stated here.** The hypothesis bundle the result quantifies
over is `Ttc.TtcProb` (`Ttc/TtcProb.lean`), which is an abstract interface —
`CLAUDE.md` §1's layer 1 — and not part of the problem. The two *other papers'*
assumption bundles it names are `Ttc.VolumeAlgorithm` (`Volume/Oracle`) and
`Ttc.KV97Sampler` (`Sampler/Interface`).
-/

namespace Ttc

/-- **The paper's `Vol(F)`**: the Lebesgue volume of the solution set. This is
what `TTC` approximates. -/
noncomputable def volSol {A : Type*} {n : ℕ} (M : A → Set (Space n)) (φ : BForm A) : ℝ :=
  (MeasureTheory.volume (sol M φ)).toReal

/-- **The multiplicative relative-error interval** `(1 ± ε)·b = [(1−ε)b, (1+ε)b]`
— the paper's notation `a ∈ (1 ± ε)·b`. This is the sense in which `TTC` is
accurate: it returns a value in `relErr ε (volSol M φ)` with probability
`≥ 1 − δ`. Marked `@[reducible]` so it is definitionally transparent to
`Set.Icc`, which is how the development unfolds it (`simp only [relErr,
Set.mem_Icc]`). -/
@[reducible] def relErr (ε b : ℝ) : Set ℝ := Set.Icc ((1 - ε) * b) ((1 + ε) * b)

end Ttc
