/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# `Model/Pseudocode`: `alg:ttc` transcribed

A line-by-line model of Algorithm 1's main loop, so that an auditor can read the
control flow rather than take it on trust. Line numbers below refer to
`sections/algo.tex`. Place `algo.tex` in one window and this file in the other
and check them line by line.

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

**There are no proofs in this file.** The structural invariants of the modelled
execution are in `Analysis/Invariants`.

## What is modelled, and what is not

**Modelled exactly**: the state `(X, p)`, the order of operations, the two
`while` conditions, the coverage filter, and the final `|X|/p`.

**Abstracted into `Ttc.Oracles`**: the four external calls — `Vol_ED`, the
Poisson draw, `GenerateSamples`, and the fair-coin thinning. Each is a *field*,
so the state evolution here is deterministic **given the oracle's answers**. This
is deliberate and is exactly where the probabilistic content lives: the
distribution of the output is `lem:numlattice`, which this development assumes
(see the README). Nothing here claims anything about that distribution.

**Fuel, not termination proofs.** Both `while` loops are given an explicit
iteration budget. The first loop's budget is computable in closed form
(`p` halves each time until `p < Thresh/t`); the second depends on fresh Poisson
draws, so no closed form exists. Running out of fuel returns the current state,
so every theorem in `Analysis/Invariants` is a statement about the *modelled*
execution.

**The link to the headline theorem is a hypothesis, not a theorem.**
`Ttc.TtcAnalysis` (`Model/Prelude`) takes its output `est` as a *field*
satisfying `lem:numlattice`'s conclusion; that `run` satisfies it **is**
`lem:numlattice`, which is assumed. The link is written out as
`Ttc.TtcAnalysis.IsOutputOf`, and `Ttc.TtcAnalysis.run_volume_estimate`
(`Model/Theorem`) states the guarantee for `run` under it. So until that
hypothesis is discharged, this file documents the algorithm rather than forming
part of the trusted base of the unconditional headline. The README says so in the
same words.
-/

namespace Ttc

open Multiset

variable {n : ℕ} {ι : Type*}

/-- The mutable state of the main loop: the sample multiset `X` and the rate `p`. -/
structure SketchState (n : ℕ) where
  /-- The multiset `𝒳` of retained lattice points. -/
  X : Multiset (Space n)
  /-- The current sampling rate `p`. -/
  p : ℝ

/-- The external calls Algorithm 1 makes, as an oracle bundle.

Making these fields rather than definitions is the honest modelling choice: their
*distributions* are what `lem:numlattice` is about, and that is assumed here. -/
structure Oracles (n : ℕ) (ι : Type*) where
  /-- `Vol_ED(P(cᵢ), ε', δ')` — the polytope volume estimate (line 24). -/
  vol : ι → ℝ
  /-- Membership test `s ∈ P(cᵢ)` (line 27). -/
  covered : Space n → ι → Bool
  /-- "Remove every element of `X` with probability ½" (lines 33, 40). -/
  halve : Multiset (Space n) → Multiset (Space n)
  /-- Thinning cannot increase the size of `X`. -/
  halve_card_le : ∀ X, card (halve X) ≤ card X
  /-- A draw from `Pois(λ)` (lines 38, 41). -/
  pois : ℝ → ℕ
  /-- `GenerateSamples(P(cᵢ), N, ρ)` (line 43). -/
  gen : ι → ℕ → Multiset (Space n)
  /-- `GenerateSamples` returns exactly `N` points. -/
  gen_card : ∀ i N, card (gen i N) = N

variable (P : Params) (O : Oracles n ι)

/-! ## The loop body -/

/-- **Lines 26–30.** Drop from `X` every point already covered by `P(cᵢ)`. -/
def dropCovered (i : ι) (X : Multiset (Space n)) : Multiset (Space n) :=
  X.filter fun s => O.covered s i = false

/-- **Lines 32–35.** `while p ≥ Thresh/t do (X ← halve X ; p ← p/2)`. -/
noncomputable def halveDown (t : ℝ) : ℕ → SketchState n → SketchState n
  | 0, st => st
  | f + 1, st =>
      if P.thresh / t ≤ st.p then halveDown t f ⟨O.halve st.X, st.p / 2⟩ else st

/-- **Lines 39–42.** `while Nᵢ + |X| > Thresh do (X ← halve X ; Nᵢ ← Pois(t·p/2) ; p ← p/2)`. -/
noncomputable def absorb (t : ℝ) : ℕ → SketchState n × ℕ → SketchState n × ℕ
  | 0, s => s
  | f + 1, (st, N) =>
      if P.thresh < (N : ℝ) + card st.X then
        absorb t f (⟨O.halve st.X, st.p / 2⟩, O.pois (t * st.p / 2))
      else (st, N)

/-- **One iteration of the main loop (lines 24–44).** `fuel` bounds both `while`s. -/
noncomputable def step (fuel : ℕ) (st : SketchState n) (i : ι) : SketchState n :=
  let t := O.vol i
  let st₁ : SketchState n := ⟨dropCovered O i st.X, st.p⟩
  let st₂ := halveDown P O t fuel st₁
  let res := absorb P O t fuel (st₂, O.pois (t * st₂.p))
  ⟨res.1.X + O.gen i res.2, res.1.p⟩

/-- **The whole algorithm (lines 22–46).** Fold `step` over the cubes from
`X = ∅, p = 1`, then output `|X|/p`. -/
noncomputable def run (fuel : ℕ) (cubes : List ι) : ℝ :=
  let final := cubes.foldl (step P O fuel) ⟨0, 1⟩
  (card final.X : ℝ) / final.p

/-! ## The faithfulness bridge

The `est` field of `Ttc.TtcAnalysis` (`Model/Prelude`) is a bare real. Nothing in
that structure says it is what the *algorithm* outputs — and a guarantee about an
unconstrained real is a guarantee about nothing.
`Ttc.TtcAnalysis.IsOutputOf` is that missing link, written as an **explicit
hypothesis** rather than left to the field's name and docstring. It lives here,
next to `Ttc.run`, because it is the one statement that mentions both sides.

This is the one place where this development differs structurally from a
completed formalisation. The pattern to aim at has *two* models of the algorithm
— a paper-faithful transcription and the operational one the analysis reasons
about — joined by a **proved** bridge, which is what puts the operational model
outside the trusted base. Here there is only the transcription, and the bridge is
*assumed*, because proving it is exactly `lem:numlattice`. So it sits in
`Model/`, with the other assumptions, rather than in `Analysis/` with the proofs.

Stating it explicitly buys two things. `Ttc.TtcAnalysis.run_volume_estimate`
(`Model/Theorem`) is a guarantee about `Ttc.run` — the transcribed algorithm —
and not about a free variable; and the hypothesis is satisfiable
(`Ttc.exists_isOutputOf`), so that theorem is not vacuous. -/
def TtcAnalysis.IsOutputOf {A : Type*} (T : TtcAnalysis A n)
    (P : Params) (O : Oracles n (Cube A)) (fuel : ℕ) : Prop :=
  T.est = run P O fuel T.D

end Ttc
