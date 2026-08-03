/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# `Model/Pseudocode`: `alg:ttc`

A line-by-line transcription of Algorithm 1. Put `sections/algo.tex` beside this
file and check the control flow. No proofs; the structural invariants of the
modelled execution are in `Analysis/Invariants`.

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

Three deviations, all deliberate.

**The four external calls are fields of `Ttc.Oracles`**, so the state evolution is
deterministic given their answers — all the randomness sits at that boundary,
which is where `lem:numlattice` lives.

**Every randomised call is indexed by a `clock`**, a counter of how many draws the
run has consumed, carried in `Ttc.SketchState`. The pseudocode has no such
counter; it is here because without it the model cannot express what the
algorithm does. `halve : ℕ → Multiset → Multiset` applied twice to the *same*
multiset must be allowed to give different answers — the algorithm flips fresh
coins each time — and an unindexed `halve : Multiset → Multiset` cannot: once a
thinning happens to be a no-op, every later thinning of that multiset is forced
to be the same no-op, so `𝒳` would never shrink again. The same applies to
`pois` at a repeated rate. Distinct call sites get distinct clock values
(`Ttc.halveDown_clock`, `Ttc.absorb_clock`, `Ttc.step_clock`), which is what lets
a distributional hypothesis say the draws are independent.

**Both `while` loops run on explicit fuel**: running out returns the current
state, so no termination is claimed (none is available — the second loop
terminates only with high probability). Note that this makes the *accuracy* of
the output conditional on the fuel being adequate.
-/

namespace Ttc

open Multiset

variable {n : ℕ} {ι : Type*}

/-- The loop state: the sample multiset `X`, the rate `p`, and the `clock`
counting oracle draws consumed so far. `X` and `p` are the paper's state; the
clock is bookkeeping for the randomness (see the module docstring). -/
structure SketchState (n : ℕ) where
  /-- The multiset `𝒳` of retained lattice points. -/
  X : Multiset (Space n)
  /-- The current sampling rate `p`. -/
  p : ℝ
  /-- How many randomised oracle calls the run has made so far. Not part of the
  algorithm: it names the draw, so that distinct calls are distinct draws. -/
  clock : ℕ
  /-- The **level**: `p = 2^(-level)`. Incremented by every halving, and passed to
  the randomised oracles so that a draw can be identified with its epoch — see the
  `gen` field and README finding 15. -/
  level : ℕ

/-- The four external calls, as fields. Their *distributions* are what
`lem:numlattice` is about, and that is assumed. -/
structure Oracles (n : ℕ) (ι : Type*) where
  /-- `Vol_ED(P(cᵢ), ε', δ')` (line 24). -/
  vol : ι → ℝ
  /-- Membership test `s ∈ P(cᵢ)` (line 27). -/
  covered : Space n → ι → Bool
  /-- "Remove every element of `X` with probability ½" (lines 33, 40), at draw
  number `c`. -/
  halve : ℕ → ℕ → Multiset (Space n) → Multiset (Space n)
  /-- Thinning **removes** elements: the result is a sub-multiset. Stronger than
  "the cardinality does not grow", and it is what the pseudocode says — the loop
  deletes elements of `X`, it never invents them. -/
  halve_le : ∀ c j X, halve c j X ≤ X
  /-- A draw from `Pois(λ)` (lines 38, 41), at draw number `c`, for cube `i` at
  level `j`. **Deviation from `algo.tex:38,41`**: the draw is told which cube and
  which level it belongs to; see the `gen` field. -/
  pois : ℕ → ι → ℕ → ℝ → ℕ
  /-- `GenerateSamples(P(cᵢ), N, ρ)` (line 43), at draw number `c`: `N` points of
  `P(cᵢ) ∩ 𝕃ⁿ`, where the lattice `𝕃ⁿ = 10^(-ρ)·ℤⁿ` is fixed by `ρ`.

  **Deviation from `algo.tex:43`**: the sampler is also told the current level `j`;
  the pseudocode's is not. It is needed because `lem:numlattice`'s `Err(j)` must be
  an event about a level-`j` process coupled to the run, and a rate-blind sampler
  cannot realise that coupling — see README finding 15 and `AUDIT.md`. -/
  gen : ℕ → ι → ℕ → ℕ → ℤ → Multiset (Space n)
  /-- `GenerateSamples` returns exactly `N` points. -/
  gen_card : ∀ c i j N ρ, card (gen c i j N ρ) = N

variable (P : Params) (O : Oracles n ι)

/-- **Lines 26–30.** Drop from `X` every point already covered by `P(cᵢ)`. -/
def dropCovered (i : ι) (X : Multiset (Space n)) : Multiset (Space n) :=
  X.filter fun s => O.covered s i = false

/-- **Lines 32–35.** `while p ≥ Thresh/t do (X ← halve X ; p ← p/2)`, on fuel.
Each iteration consumes one draw. -/
noncomputable def halveDown (t : ℝ) : ℕ → SketchState n → SketchState n
  | 0, st => st
  | f + 1, st =>
      if P.thresh / t ≤ st.p then
        halveDown t f ⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 1, st.level + 1⟩
      else st

/-- **Lines 39–42.** `while Nᵢ + |X| > Thresh do (X ← halve X ; Nᵢ ← Pois(t·p/2) ; p ← p/2)`,
on fuel. Each iteration consumes two draws: the thinning, then the Poisson. -/
noncomputable def absorb (i : ι) (t : ℝ) : ℕ → SketchState n × ℕ → SketchState n × ℕ
  | 0, s => s
  | f + 1, (st, N) =>
      if P.thresh < (N : ℝ) + card st.X then
        absorb i t f (⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 2, st.level + 1⟩,
                    O.pois (st.clock + 1) i (st.level + 1) (t * st.p / 2))
      else (st, N)

/-- **Lines 24–42.** The state after both `while` loops of iteration `i`, paired
with the surviving Poisson draw `Nᵢ`. Split out of `Ttc.step` so that the
`GenerateSamples` append can be stated on its own (`Ttc.card_step`). -/
noncomputable def stepPre (fuel : ℕ) (st : SketchState n) (i : ι) : SketchState n × ℕ :=
  let t := O.vol i
  let st₂ := halveDown P O t fuel ⟨dropCovered O i st.X, st.p, st.clock, st.level⟩
  absorb P O i t fuel (⟨st₂.X, st₂.p, st₂.clock + 1, st₂.level⟩,
    O.pois st₂.clock i st₂.level (t * st₂.p))

/-- **Lines 24–44.** One iteration of the main loop; `fuel` bounds both `while`s
and `ρ` is the precision fixed at line 17. -/
noncomputable def step (fuel : ℕ) (ρ : ℤ) (st : SketchState n) (i : ι) : SketchState n :=
  let res := stepPre P O fuel st i
  ⟨res.1.X + O.gen res.1.clock i res.1.level res.2 ρ, res.1.p, res.1.clock + 1, res.1.level⟩

/-- **Lines 22–46.** Fold `step` over the cubes from `X = ∅, p = 1`, output `|X|/p`.
`ρ` is `GetPrecision`'s output (line 17), fixed before the loop and passed to every
`GenerateSamples` call. The clock starts at `0`. -/
noncomputable def run (fuel : ℕ) (ρ : ℤ) (cubes : List ι) : ℝ :=
  let final := cubes.foldl (step P O fuel ρ) ⟨0, 1, 0, 0⟩
  (card final.X : ℝ) / final.p

/-- **The output as a random variable**: `run` with the oracles drawn at `ω`.
This is the quantity `thm:volumettc` bounds. -/
noncomputable def ttcOutput {Ω : Type} (P : Params) (O : Ω → Oracles n ι) (fuel : ℕ)
    (ρ : ℤ) (cubes : List ι) (ω : Ω) : ℝ :=
  run P (O ω) fuel ρ cubes

end Ttc
