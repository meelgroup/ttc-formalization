/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Capstone
import Ttc.Model.ProblemSetting

/-!
# `Model/Theorem`: the headline theorem

The **statement layer**: three one-line theorems, and no proof to work through.
`thm:volumettc` of *Efficient Volume Computation for SMT Formulas*:

> Given `F` and `ε, δ ∈ (0,1]`, `TTC` returns an estimate `est` of `Vol(F)` such
> that with probability at least `1 − δ`,
> `est ∈ [(1−ε)·Vol(F), (1+ε)·Vol(F)]`.

**Audit path — read `Model/`, then stop.** `Model/Prelude` (the vocabulary: the
ambient space, formula syntax and semantics, the parameter block — every
non-Mathlib symbol the other `Model/` files use in a definition),
`Model/ProblemSetting` (what `Vol(F)` is, and `thm:decomposition`),
`Model/Pseudocode` (`alg:ttc` transcribed line by line),
this file. Every assumption is a field of `Ttc.TtcAnalysis` (`Model/Prelude`).
Nothing in `Model/` refers to a definition outside `Model/` except Mathlib.

Three things an auditor should check here, all visible without leaving the file:

1. **The capstone is about the real object.** The bound is stated for
   `Ttc.volSol T.M T.φ = (volume (sol T.M T.φ)).toReal` — the Lebesgue volume of
   the solution set of the actual SMT(LRA) formula, not of a surrogate.
2. **That set is what the algorithm enumerates.** `Ttc.TtcAnalysis.sol_eq_union`
   records that it is exactly the union of the cubes' regions
   (`thm:decomposition`), so the quantity the algorithm targets and the quantity
   the theorem bounds are the same set.
3. **The quantification is not vacuous.** `Ttc.nonempty_ttcAnalysis` inhabits the
   interface, and `Ttc.TtcAnalysis.ideal` (`Analysis/Capstone`) does so for *any*
   formula, *any* DNF representation of it and *any* `ε ∈ (0,1]`.

What is **not** claimed: the `1 − δ` failure probability is carried by the
`sketch_*` fields rather than re-derived, and nothing here is about running time.
`Model/Prelude` states the scope precisely; the README states it again.

`sorry`-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ttc

open MeasureTheory Set

namespace TtcAnalysis

variable {A : Type*} {n : ℕ} (T : TtcAnalysis A n)

/-- **`thm:decomposition` inside the interface.** The set whose volume `thm:volumettc`
bounds is exactly the union of the polytopes the algorithm enumerates. -/
theorem sol_eq_union : ⋃ c ∈ T.D, region T.M c = sol T.M T.φ :=
  sol_eq_iUnion_region T.isDNF

/-- **`thm:volumettc`.** On the event that `lem:numlattice`'s guarantee holds,
`TTC`'s output is a relative `ε`-approximation of the Lebesgue volume of the
solution set of the input SMT(LRA) formula.

The proof is the pair of chains in `Analysis/Capstone`. -/
theorem volume_estimate :
    T.est ∈ Set.Icc ((1 - T.ε) * volSol T.M T.φ) ((1 + T.ε) * volSol T.M T.φ) :=
  ⟨T.le_est, T.est_le⟩

/-- **`thm:volumettc`, about the transcribed algorithm.** Under the faithfulness
bridge — `T.est` is what `Ttc.run` (`Model/Pseudocode`, `alg:ttc` lines 22–46)
outputs on the run `(P, O, fuel)` — the same two-sided bound holds of `run`
itself rather than of a free real.

The bridge is a hypothesis, not a theorem: proving it *is* `lem:numlattice`. It
is satisfiable (`Ttc.exists_isOutputOf`), so this is not vacuous. -/
theorem run_volume_estimate (P : Params) (O : Oracles n (Cube A)) (fuel : ℕ)
    (h : T.IsOutputOf P O fuel) :
    run P O fuel T.D ∈
      Set.Icc ((1 - T.ε) * volSol T.M T.φ) ((1 + T.ε) * volSol T.M T.φ) :=
  h ▸ T.volume_estimate

end TtcAnalysis

/-- `Ttc.TtcAnalysis` is inhabited: the single-atom formula with the ideal
instance. So `Ttc.TtcAnalysis.volume_estimate` is not vacuously quantified. -/
theorem nonempty_ttcAnalysis {A : Type*} {n : ℕ} (a : A) : Nonempty (TtcAnalysis A n) :=
  ⟨TtcAnalysis.ideal (ε := 1) one_pos le_rfl (fun _ => ∅) (.atom a) [[⟨a, true⟩]]
    (by intro v; simp [DNF.holds, Cube.holds, Lit.holds, BForm.holds])⟩

#print axioms TtcAnalysis.volume_estimate

end Ttc
