/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Capstone
import Ttc.Coupling.NumLattice
import Ttc.Access

/-!
# `Estimate`: `thm:volumettc` and `thm:runtime` over the abstract bundle

The **interface layer**'s two conclusions (`CLAUDE.md` §1, layer 2): the headline
proved over an arbitrary `Ttc.TtcProb`, i.e. over *any* set of objects satisfying
its fields.

These two theorems used to live in `Ttc/Model/Theorem.lean`.  They were moved out
because their statements name the bundle's oracle field `T.O` and its precision
field `T.ρ`, and `Model/` states the problem and the guarantee over the
algorithm's own inputs `(M, φ, ε, δ)` — with the precision *computed* by
`GetPrecision` rather than supplied.  That statement is `Ttc.ttc_volume`
(`Model/Theorem.lean`); this file is the machinery it is proved from, kept
because `Ttc/Coupling/Product.lean` and everything downstream of it consume
`Ttc.TtcProb.volume_estimate` directly.

Reading order: this is *not* the audit path.  A reader auditing what is claimed
should read `Model/Prelude` → `Model/ProblemSetting` → `Model/Pseudocode` →
`Model/Theorem` and stop; this file is proof content.

`sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ttc

open MeasureTheory Set

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n) {ω : T.Ω}

/-- **`thm:volumettc`, over the abstract bundle.** With probability at least
`1 − δ`, `TTC`'s output lies within a relative `ε` of `Vol(F)`.

**Both sides are about the input formula.** `TTC` takes only `(F, ε, δ)`, so
nothing else appears here. The SMT(LRA) formula `F` is `T.atoms` together with
`T.φ` — its atoms as linear constraints, and the Boolean structure over them
(`alg:ttc` line 15). What the main loop enumerates is `T.toDNF T.φ`, the output of
the circuit-AllSAT call at line 16, *computed from `F`* rather than supplied
alongside it; `T.isDNF` is the assumption that the external tool got it right, and
that `⋃ᵢ P(cᵢ)` is then exactly `Sol(F)` is `Ttc.TtcProb.sol_eq_union`
(`Capstone`, `thm:decomposition`) — proved, not assumed.

`ttcOutput` is `Ttc.run` — the transcription of `alg:ttc` — with the oracles drawn
at `ω`; `volSol T.M T.φ` is the Lebesgue volume of the *formula's* solution set;
`relErr` is the paper's `(1 ± ε)` interval. No side hypothesis: everything rests on
the fields of `Ttc.TtcProb`, inhabited non-degenerately by
`Ttc.Box.nonempty_ttcProb`.

**This statement still names the bundle's `T.O` and `T.ρ`**, i.e. an *assumed*
oracle and an *assumed* precision. Both are discharged downstream: the
oracle-free statement over `(M, φ, ε, δ)`, with the precision computed by
`Ttc.Params.precision` (`GetPrecision`), is `Ttc.ttc_volume`
(`Model/Theorem.lean`).

Proof: at every `ω` satisfying `lem:numlattice` the deterministic chain of
`Capstone` applies, so the good event contains the `numlattice` event and
`measure_mono` carries the `1 − δ` across. -/
theorem volume_estimate :
    1 - T.δ ≤
      (T.μ {ω | ttcOutput T.P T.O T.toDNF T.ρ T.φ ω
        ∈ relErr T.ε (volSol T.M T.φ)}).toReal := by
  haveI := T.mΩ
  haveI := T.isProb
  refine le_trans T.numlattice
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_))
  intro ω hω
  exact (T.toAnalysis hω).volume_estimate

/-- **`thm:runtime`, over the abstract bundle.** The main loop runs `m` times — `m`
being the number of cubes the AllSAT call returned — and each iteration is charged
one `Vol_ED` call plus one `GenerateSamples` draw per point returned, so the run
costs at most `m · (cVol + cSample · Thresh)`.

Instantiating `cVol` at the paper's `O(n⁴)` and `cSample` at `O(n³)` gives
`m · O(n⁴)`, which is `thm:runtime` as stated.

**Two things this says that the paper does not.**

*It assumes the loops terminate.* `Ttc.Terminates` is the hypothesis that the
absorption loop of every iteration reaches a level where `Nᵢ + |𝒳| ≤ Thresh`.
Without it `Nᵢ` is unbounded and no time bound holds; the paper never states it,
and it is not provable — the real loop exits only with high probability.

*It charges only what the paper charges.* The thinning and Poisson work of the two
`while` loops is **not** in `Ttc.runCost`. The paper omits it as dominated, but the
number of those calls is exactly the unbounded quantity above, so "dominated" is
not a theorem — here or there. What is proved is the paper's own accounting, made
explicit. -/
theorem runtime (cVol cSample : ℕ) (thr : ℕ) (hthr : (thr : ℝ) = T.P.thresh)
    (hterm : Terminates T.P (T.O ω) T.D) :
    runCost T.P (T.O ω) cVol cSample T.ρ T.D
      ≤ T.numCubes * (cVol + cSample * thr) :=
  runCost_le T.P (T.O ω) cVol cSample T.ρ T.D thr hthr hterm

end TtcProb

#print axioms TtcProb.volume_estimate
#print axioms TtcProb.runtime

-- (`Vol_ED`'s contract, the former field re-derived, and the union bound over the
-- `m` calls are checked in `Ttc/Volume/Bridge.lean`, where they are proved.)

end Ttc
