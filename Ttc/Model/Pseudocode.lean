/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# `Model/Pseudocode`: `alg:ttc`

A line-by-line transcription of Algorithm 1. Put `sections/algo.tex` beside this
file and check the control flow. No proofs; the structural invariants of the
modelled execution are in `Invariants`.

```
line 22        p ← 1 ;  X ← ∅
lines 23–45    for i = 1 to m:
line 24          t ← Vol_ED(P(cᵢ), ε', δ')
lines 26–30      for s ∈ X: if s ∈ P(cᵢ) then remove s from X
lines 32–35      while p ≥ Thresh/t: remove each element of X w.p. ½ ; p ← p/2
line 38          Nᵢ ← Pois(t·p)
lines 39–42      while Nᵢ + |X| > Thresh:
                     remove each element of X w.p. ½ ; Nᵢ ← Pois(t·p/2) ; p ← p/2
line 43          S ← GenerateSamples(P(cᵢ), Nᵢ, ρ)
line 44          X ← X ⊎ S
line 46        output |X| / p
```

Throughout, the state after a cube is `Ttc.SketchState`: the multiset `𝒳` and the
**level** `j`, with `p = 2^(−j)`. The level is carried instead of `p` so that the
rate is an index rather than a real number — every randomised call is a read-off
at a level, and the paper's `Nois(j)` and `Err(j)` are events about that index.

| line | Lean |
| --- | --- |
| 22 (`p ← 1`) | level `0`: the second component of the initial `⟨0, 0⟩` |
| 22 (`X ← ∅`) | the first component of `⟨0, 0⟩` |
| 23–45 (`for i`) | `List.foldl` of `Ttc.step` over the cube list |
| 24 (`Vol_ED`) | `Ttc.Oracles.vol` |
| 26–30 (removal) | `Ttc.dropCovered`, a filter on `Ttc.Oracles.covered` |
| 32–35 (`while`) | `Ttc.haltLevel` — the least level at which the guard fails |
| 38 (`Pois(t·p)`) | `Ttc.Oracles.pois i j (t·2^(−j))` at the exit level |
| 39–42 (`while`) | `Ttc.absorbLevel` — the least level at which the guard fails |
| 39–42 (thinning) | `Ttc.Oracles.thin j₀ j'`, the survivors at level `j'` |
| 43 (`GenerateSamples`) | `Ttc.Oracles.gen` |
| 44 (`X ⊎ S`) | the `+` in `Ttc.step` |
| 46 (output) | `Ttc.run`, and `Ttc.ttcOutput` as a random variable |

**The four external calls are fields of `Ttc.Oracles`**, so the state evolution is
deterministic given their answers — all the randomness sits at that boundary,
which is where `lem:numlattice` lives.

## Four deviations from `algo.tex`

These are the places where the Lean development does not say quite what the paper
says. They are recorded here, because this is the file a reader consults to check
the modelling.

**(a) The `while` loops are exit levels, not iterations.** Neither loop is written
as a recursion. `Ttc.haltLevel` and `Ttc.absorbLevel` are the **least level at or
above the current one at which the loop's guard fails**, an `sInf` over `ℕ`, and
the step jumps straight there. This is what the loops compute when they terminate,
and it needs no termination proof — which matters, because the second loop has
none to give: it exits when repeated thinning brings `Nᵢ + |𝒳|` under `Thresh`,
which happens only with high probability. A fuelled recursion would have been the
alternative, and it forces an iteration budget into the statement of the main
theorem; this does not.

**(b) An empty exit set exits immediately.** When no level satisfies the exit
condition — the run where the algorithm loops forever — the set that
`Ttc.absorbLevel` takes an `sInf` over is empty, `Nat.sInf` returns `0` by
convention, and the `max` with the entry level degenerates to "stay put". Nothing
depends on this corner: every consequence drawn from an exit level is of the form
"every level strictly below it had the guard true" (`Ttc.lt_haltLevel`,
`Ttc.lt_absorbLevel`), which is vacuously true when the loop does not move.

**(c) The thinning is a read-off at a level, not a repeated coin.**
`Ttc.Oracles.thin j₀ j' X` is the sub-multiset of `X` that survives down to level
`j'`, having entered the step at level `j₀` — one call, not `j' − j₀` of them. This
is what lets the loops be exit levels: the guard at a candidate level `j'` can be
evaluated without running the loop to get there. The only law assumed of it is
`Ttc.Oracles.thin_le`: thinning **removes** copies, never invents them. Note that
`thin j₀ j₀` is a no-op on the states the run reaches, but is not assumed to be the
identity outright — the concrete family in `Coupling/Family` realises it as a cap
against the level-`j₀` counts, which is the identity exactly there.

**(d) The randomised calls are told the cube and the level.** `pois` takes `(i, j)`
and `gen` takes `(i, j)`, where `algo.tex:38,41,43` pass neither. The index is what
names the draw: two calls with different `(i, j)` are different draws, which is
what a distributional hypothesis needs in order to speak of independence. The level
in particular is needed because `lem:numlattice`'s `Err(j)` must be an event about a
level-`j` process coupled to the run, and a level-blind sampler cannot realise that
coupling — see README finding 15 and `AUDIT.md`.
-/

namespace Ttc

open Multiset

variable {n : ℕ} {ι : Type*}

/-- The loop state: the sample multiset `X` and the **level** `j`, with `p = 2^(−j)`.
`X` is the paper's `𝒳`; the level is the paper's `p`, carried as its exponent so
that the rate is an index the randomised oracles can be told (see the module
docstring). -/
structure SketchState (n : ℕ) where
  /-- The multiset `𝒳` of retained lattice points. -/
  X : Multiset (Space n)
  /-- The **level**: `p = 2^(−level)`. Incremented by every halving. -/
  level : ℕ

namespace SketchState

/-- The paper's sampling rate `p = 2^(−level)`. A definition, not a field: `p` is
only ever `1` halved some number of times, so the level determines it. -/
noncomputable def p (st : SketchState n) : ℝ := (1 / 2 : ℝ) ^ st.level

@[simp] theorem p_mk (X : Multiset (Space n)) (j : ℕ) :
    (⟨X, j⟩ : SketchState n).p = (1 / 2 : ℝ) ^ j := rfl

end SketchState

/-- The four external calls, as fields. Their *distributions* are what
`lem:numlattice` is about, and that is assumed. -/
structure Oracles (n : ℕ) (ι : Type*) where
  /-- `Vol_ED(P(cᵢ), ε', δ')` (line 24). -/
  vol : ι → ℝ
  /-- Membership test `s ∈ P(cᵢ)` (line 27). -/
  covered : Space n → ι → Bool
  /-- "Remove every element of `X` with probability ½", iterated (lines 33, 40):
  `thin j₀ j' X` is what survives of `X` at level `j'`, entering at level `j₀`.
  See deviation (c). -/
  thin : ℕ → ℕ → Multiset (Space n) → Multiset (Space n)
  /-- Thinning **removes** elements: the result is a sub-multiset. Stronger than
  "the cardinality does not grow", and it is what the pseudocode says — the loop
  deletes elements of `X`, it never invents them. -/
  thin_le : ∀ j₀ j' X, thin j₀ j' X ≤ X
  /-- A draw from `Pois(λ)` (lines 38, 41), for cube `i` at level `j`. -/
  pois : ι → ℕ → ℝ → ℕ
  /-- `GenerateSamples(P(cᵢ), N, ρ)` (line 43), for cube `i` at level `j`: `N`
  points of `P(cᵢ) ∩ 𝕃ⁿ`, where the lattice `𝕃ⁿ = 10^(-ρ)·ℤⁿ` is fixed by `ρ`. -/
  gen : ι → ℕ → ℕ → ℤ → Multiset (Space n)
  /-- `GenerateSamples` returns exactly `N` points. -/
  gen_card : ∀ i j N ρ, card (gen i j N ρ) = N

variable (P : Params) (O : Oracles n ι)

/-- **Lines 26–30.** Drop from `X` every point already covered by `P(cᵢ)`. -/
def dropCovered (i : ι) (X : Multiset (Space n)) : Multiset (Space n) :=
  X.filter fun s => O.covered s i = false

/-- **Lines 32–35.** `while p ≥ Thresh/t do (X ← halve X ; p ← p/2)`, as its exit
level: the least level at or above `j` whose rate `2^(−j')` is below `Thresh/t`.
Deterministic — no randomness enters this loop, only the rate. -/
noncomputable def haltLevel (t : ℝ) (j : ℕ) : ℕ :=
  max j (sInf {j' | ¬ P.thresh / t ≤ (1 / 2 : ℝ) ^ j'})

/-- **Lines 39–42.** `while Nᵢ + |X| > Thresh do (X ← halve X ; Nᵢ ← Pois(t·p/2) ; p ← p/2)`,
as its exit level: the least level `j'` at or above `j₁` at which the surviving
sketch and the level-`j'` Poisson draw together fit under `Thresh`. `j₀` is the
level the step was entered at, which is what `thin` measures survival from. -/
noncomputable def absorbLevel (i : ι) (t : ℝ) (X : Multiset (Space n)) (j₀ j₁ : ℕ) : ℕ :=
  max j₁ (sInf {j' | j₁ ≤ j' ∧ ¬ P.thresh <
    (O.pois i j' (t * (1 / 2 : ℝ) ^ j') : ℝ) + (card (O.thin j₀ j' X) : ℝ)})

/-- **Lines 24–42.** The state after both `while` loops of iteration `i`, paired
with the surviving Poisson draw `Nᵢ`. Split out of `Ttc.step` so that the
`GenerateSamples` append can be stated on its own (`Ttc.card_step`). -/
noncomputable def stepPre (st : SketchState n) (i : ι) : SketchState n × ℕ :=
  let t := O.vol i
  let X₀ := dropCovered O i st.X
  let j := absorbLevel P O i t X₀ st.level (haltLevel P t st.level)
  (⟨O.thin st.level j X₀, j⟩, O.pois i j (t * (1 / 2 : ℝ) ^ j))

/-- **Lines 24–44.** One iteration of the main loop; `ρ` is the precision fixed at
line 17. -/
noncomputable def step (ρ : ℤ) (st : SketchState n) (i : ι) : SketchState n :=
  let res := stepPre P O st i
  ⟨res.1.X + O.gen i res.1.level res.2 ρ, res.1.level⟩

/-- **Lines 22–46.** Fold `step` over the cubes from `X = ∅` at level `0`, output
`|X|/p`. `ρ` is `GetPrecision`'s output (line 17), fixed before the loop and passed
to every `GenerateSamples` call. -/
noncomputable def run (ρ : ℤ) (cubes : List ι) : ℝ :=
  let final := cubes.foldl (step P O ρ) ⟨0, 0⟩
  (card final.X : ℝ) / final.p

/-- **`TTC(F, ε, δ)`'s output, as a random variable over the input formula.**

The algorithm's **input is the formula**: there is no DNF argument. The cube list
the main loop folds over is `toDNF φ`, produced here by the line-16 converter from
`φ`, `F`'s Boolean abstraction (line 15). `P` is the parameter block of lines
17–20, `ρ` is `GetPrecision`'s output (line 17), and `O ω` are the oracles drawn at
the sample point `ω`.

`toDNF` is a *parameter* rather than the fixed `Ttc.toDNF` of `Model/Prelude`
because `TTC` runs an optimised circuit AllSAT, and `thm:runtime` is stated in
terms of `m`, **that** procedure's cube count — pinning the converter would prove
the guarantee for a different, generally exponentially larger `m`. Correctness
holds for any converter meeting `Ttc.IsDNFOf`, and `Ttc.toDNF_isDNFOf` shows at
least one does, so the parameter is not an empty hypothesis.

This is the quantity `thm:volumettc` bounds; `Ttc.runCost` is what `thm:runtime`
bounds, over the same run. -/
noncomputable def ttcOutput {A : Type*} {Ω : Type} (P : Params)
    (O : Ω → Oracles n (Cube A)) (toDNF : BForm A → DNF A) (ρ : ℤ)
    (φ : BForm A) (ω : Ω) : ℝ :=
  run P (O ω) ρ (toDNF φ)

end Ttc
