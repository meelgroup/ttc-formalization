/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Capstone
import Ttc.Analysis.NumLattice

/-!
# `Model/Theorem`: `thm:volumettc`

> Given `F` and `ε, δ ∈ (0,1]`, `TTC` returns an estimate of `Vol(F)` such that
> with probability at least `1 − δ`, `est ∈ [(1−ε)·Vol(F), (1+ε)·Vol(F)]`.

Audit path: `Model/Prelude` (vocabulary) → `Model/Pseudocode` (`alg:ttc` and its
output) → `Model/ProblemSetting` (`Ttc.TtcProb`: every assumption, as fields) →
this file. Nothing in `Model/` refers to a definition outside `Model/` except
Mathlib. `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ttc

open MeasureTheory Set

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- **`thm:volumettc`.** With probability at least `1 − δ`, `TTC`'s output lies
within a relative `ε` of `Vol(F)`.

`ttcOutput` is `Ttc.run` — the transcription of `alg:ttc` — with the oracles drawn
at `ω`; `volSol` is the Lebesgue volume of the real solution set; `relErr` is the
paper's `(1 ± ε)` interval. No side hypothesis: everything rests on the fields of
`Ttc.TtcProb`, inhabited non-degenerately by `Ttc.Box.nonempty_ttcProb`. That `volSol` measures the set
the algorithm actually enumerates is `Ttc.TtcProb.sol_eq_union`
(`Analysis/Capstone`, `thm:decomposition`).

Proof: at every `ω` satisfying `lem:numlattice` the deterministic chain of
`Analysis/Capstone` applies, so the good event contains the `numlattice` event and
`measure_mono` carries the `1 − δ` across. -/
theorem volume_estimate :
    1 - T.δ ≤
      (T.μ {ω | ttcOutput T.P T.O T.fuel T.ρ T.D ω ∈ relErr T.ε (volSol T.M T.φ)}).toReal := by
  haveI := T.mΩ
  haveI := T.isProb
  refine le_trans T.numlattice
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_))
  intro ω hω
  exact (T.toAnalysis hω).volume_estimate

end TtcProb

#print axioms TtcProb.volume_estimate

end Ttc
