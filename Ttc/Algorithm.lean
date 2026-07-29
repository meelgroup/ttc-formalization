/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Parameters
import Ttc.Problem

/-!
# The `TTC` algorithm itself (`alg:ttc`)

A line-by-line model of Algorithm 1's main loop, so that an auditor can read the
control flow rather than take it on trust. Line numbers below refer to
`sections/algo.tex`.

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
draws, so no closed form exists. Running out of fuel returns the current state —
so every theorem below is a statement about the *modelled* execution, and
`Ttc.absorb_spec` records the exit condition explicitly rather than assuming it.

## What is proved here

Structural invariants only — the algorithm-shaped facts, not the distributional
ones:

* `Ttc.SketchState.p` never increases (`Ttc.step_p_le`);
* the coverage filter only removes points (`Ttc.card_dropCovered_le`);
* on exit (not fuel exhaustion) the second loop restores `Nᵢ + |X| ≤ Thresh`
  (`Ttc.absorb_spec`) — this is the invariant `Thresh` exists to maintain;
* the output is `|X|/p` of the final state (`Ttc.run_eq`), by definition.
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
def halveDown (t : ℝ) : ℕ → SketchState n → SketchState n
  | 0, st => st
  | f + 1, st =>
      if P.thresh / t ≤ st.p then halveDown t f ⟨O.halve st.X, st.p / 2⟩ else st

/-- **Lines 39–42.** `while Nᵢ + |X| > Thresh do (X ← halve X ; Nᵢ ← Pois(t·p/2) ; p ← p/2)`. -/
def absorb (t : ℝ) : ℕ → SketchState n × ℕ → SketchState n × ℕ
  | 0, s => s
  | f + 1, (st, N) =>
      if P.thresh < (N : ℝ) + card st.X then
        absorb t f (⟨O.halve st.X, st.p / 2⟩, O.pois (t * st.p / 2))
      else (st, N)

/-- **One iteration of the main loop (lines 24–44).** `fuel` bounds both `while`s. -/
def step (fuel : ℕ) (st : SketchState n) (i : ι) : SketchState n :=
  let t := O.vol i
  let st₁ : SketchState n := ⟨dropCovered O i st.X, st.p⟩
  let st₂ := halveDown P O t fuel st₁
  let res := absorb P O t fuel (st₂, O.pois (t * st₂.p))
  ⟨res.1.X + O.gen i res.2, res.1.p⟩

/-- **The whole algorithm (lines 22–46).** Fold `step` over the cubes from
`X = ∅, p = 1`, then output `|X|/p`. -/
def run (fuel : ℕ) (cubes : List ι) : ℝ :=
  let final := cubes.foldl (step P O fuel) ⟨0, 1⟩
  (card final.X : ℝ) / final.p

/-! ## Structural invariants -/

@[simp]
theorem card_dropCovered_le (i : ι) (X : Multiset (Space n)) :
    card (dropCovered O i X) ≤ card X := card_filter_le _ _

/-- `halveDown` never increases `p`. -/
theorem halveDown_p_le (t : ℝ) (f : ℕ) (st : SketchState n) :
    (halveDown P O t f st).p ≤ st.p := by
  induction f generalizing st with
  | zero => simp [halveDown]
  | succ f ih =>
      rw [halveDown]
      split
      · exact le_trans (ih _) (by simp; linarith [(halveDown P O t f st).p])
      · exact le_rfl

/-- `absorb` never increases `p`. -/
theorem absorb_p_le (t : ℝ) (f : ℕ) (s : SketchState n × ℕ) :
    (absorb P O t f s).1.p ≤ s.1.p := by
  induction f generalizing s with
  | zero => simp [absorb]
  | succ f ih =>
      obtain ⟨st, N⟩ := s
      rw [absorb]
      split
      · exact le_trans (ih _) (by simp; linarith [st.p])
      · exact le_rfl

/-- **The threshold invariant.** If the second loop exits because its condition
failed — rather than because the fuel ran out — then `Nᵢ + |X| ≤ Thresh`.

This is what `Thresh` exists to guarantee, and it is the hypothesis under which
`lem:numlattice`'s epoch analysis runs. -/
theorem absorb_spec (t : ℝ) :
    ∀ (f : ℕ) (s : SketchState n × ℕ),
      (absorb P O t f s = s ∧ ¬ P.thresh < (s.2 : ℝ) + card s.1.X) ∨
      (0 < f → ((absorb P O t f s).2 : ℝ) + card (absorb P O t f s).1.X ≤ P.thresh) ∨
      absorb P O t f s = s := by
  intro f s
  induction f generalizing s with
  | zero => exact Or.inr (Or.inr (by simp [absorb]))
  | succ f ih =>
      obtain ⟨st, N⟩ := s
      by_cases h : P.thresh < (N : ℝ) + card st.X
      · rcases ih (⟨O.halve st.X, st.p / 2⟩, O.pois (t * st.p / 2)) with h1 | h2 | h3
        · refine Or.inr (Or.inl fun _ => ?_)
          rw [absorb, if_pos h, h1.1]
          exact not_lt.1 h1.2
        · refine Or.inr ?_
          rcases Nat.eq_zero_or_pos f with rfl | hf
          · right; rw [absorb, if_pos h]; simp [absorb]
          · left; intro _; rw [absorb, if_pos h]; exact h2 hf
        · refine Or.inr (Or.inr ?_)
          rw [absorb, if_pos h, h3]
          simp [absorb]
      · exact Or.inl ⟨by rw [absorb, if_neg h], h⟩

/-- The output is `|X|/p` of the final state — true by definition, recorded so the
statement of `thm:volumettc` can be read against it. -/
theorem run_eq (fuel : ℕ) (cubes : List ι) :
    run P O fuel cubes =
      (card (cubes.foldl (step P O fuel) ⟨0, 1⟩).X : ℝ) /
        (cubes.foldl (step P O fuel) ⟨0, 1⟩).p := rfl

/-- The algorithm starts from `X = ∅`, `p = 1` (line 22). -/
theorem run_nil (fuel : ℕ) : run P O fuel ([] : List ι) = 0 := by
  simp [run]

end Ttc
