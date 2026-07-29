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
draws, so no closed form exists. Running out of fuel returns the current state,
so every theorem below is a statement about the *modelled* execution.

## What is proved here

Structural invariants only — the algorithm-shaped facts, not the distributional
ones:

* the coverage filter only removes points (`Ttc.card_dropCovered_le`);
* `p` never increases and stays nonnegative, through both loops
  (`Ttc.halveDown_p`, `Ttc.absorb_p`);
* a state whose guard already fails is a fixpoint (`Ttc.absorb_of_settled`,
  `Ttc.halveDown_of_settled`);
* the output is `|X|/p` of the final state (`Ttc.run_eq`), by definition.

**Not** proved: termination, and anything distributional. See below.
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

/-! ## Structural invariants

These are the algorithm-shaped facts: what the loop does to `X` and `p`. The
*distributional* facts — that the output concentrates around `|Q ∩ 𝕃ⁿ|/10^(ρn)` —
are `lem:numlattice`, which this development assumes.

**Termination is deliberately not claimed.** Both `while` loops run on fuel. The
real second loop terminates because repeated thinning eventually brings
`Nᵢ + |X|` under `Thresh` *with high probability*; there is no deterministic
bound, so no fuel-independent termination theorem is available — and asserting
one would be false. What is recorded instead is that a state already satisfying
the guard is a fixpoint (`Ttc.absorb_of_settled`).
-/

@[simp]
theorem card_dropCovered_le (i : ι) (X : Multiset (Space n)) :
    card (dropCovered O i X) ≤ card X :=
  card_le_card (Multiset.filter_le _ _)

@[simp]
theorem halveDown_zero (t : ℝ) (st : SketchState n) : halveDown P O t 0 st = st := rfl

@[simp]
theorem absorb_zero (t : ℝ) (s : SketchState n × ℕ) : absorb P O t 0 s = s := rfl

/-- A state whose guard already fails is a fixpoint of the absorption loop. -/
theorem absorb_of_settled (t : ℝ) (f : ℕ) (s : SketchState n × ℕ)
    (h : ¬ P.thresh < (s.2 : ℝ) + card s.1.X) : absorb P O t f s = s := by
  cases f with
  | zero => rfl
  | succ f => rw [absorb, if_neg h]

/-- Likewise for the first loop. -/
theorem halveDown_of_settled (t : ℝ) (f : ℕ) (st : SketchState n)
    (h : ¬ P.thresh / t ≤ st.p) : halveDown P O t f st = st := by
  cases f with
  | zero => rfl
  | succ f => rw [halveDown, if_neg h]

/-- **`p` never increases, and stays nonnegative**, through the first loop. -/
theorem halveDown_p (t : ℝ) (f : ℕ) (st : SketchState n) (h : 0 ≤ st.p) :
    0 ≤ (halveDown P O t f st).p ∧ (halveDown P O t f st).p ≤ st.p := by
  induction f generalizing st with
  | zero => exact ⟨h, le_rfl⟩
  | succ f ih =>
      rw [halveDown]
      split
      · have hh : (0:ℝ) ≤ st.p / 2 := by linarith
        obtain ⟨h1, h2⟩ := ih ⟨O.halve st.X, st.p / 2⟩ hh
        exact ⟨h1, le_trans h2 (by simpa using (by linarith : st.p / 2 ≤ st.p))⟩
      · exact ⟨h, le_rfl⟩

/-- **`p` never increases, and stays nonnegative**, through the second loop. -/
theorem absorb_p (t : ℝ) (f : ℕ) (s : SketchState n × ℕ) (h : 0 ≤ s.1.p) :
    0 ≤ (absorb P O t f s).1.p ∧ (absorb P O t f s).1.p ≤ s.1.p := by
  induction f generalizing s with
  | zero => exact ⟨h, le_rfl⟩
  | succ f ih =>
      obtain ⟨st, N⟩ := s
      rw [absorb]
      split
      · have hh : (0:ℝ) ≤ st.p / 2 := by simp at h; linarith
        obtain ⟨h1, h2⟩ := ih (⟨O.halve st.X, st.p / 2⟩, O.pois (t * st.p / 2)) hh
        refine ⟨h1, le_trans h2 ?_⟩
        simp at h ⊢; linarith
      · exact ⟨h, le_rfl⟩

/-- **`X` only grows by the freshly generated samples**: the loop body removes
covered points and thins, then appends exactly `Nᵢ` new ones. -/
theorem card_step_le (fuel : ℕ) (st : SketchState n) (i : ι) :
    card (step P O fuel st i).X ≤
      card (absorb P O (O.vol i) fuel
        (halveDown P O (O.vol i) fuel ⟨dropCovered O i st.X, st.p⟩,
         O.pois (O.vol i * (halveDown P O (O.vol i) fuel
           ⟨dropCovered O i st.X, st.p⟩).p))).1.X
        + (absorb P O (O.vol i) fuel
        (halveDown P O (O.vol i) fuel ⟨dropCovered O i st.X, st.p⟩,
         O.pois (O.vol i * (halveDown P O (O.vol i) fuel
           ⟨dropCovered O i st.X, st.p⟩).p))).2 := by
  simp [step, O.gen_card]

/-- The output is `|X|/p` of the final state — true by definition, recorded so
`thm:volumettc`'s statement can be read against the code. -/
theorem run_eq (fuel : ℕ) (cubes : List ι) :
    run P O fuel cubes =
      (card (cubes.foldl (step P O fuel) ⟨0, 1⟩).X : ℝ) /
        (cubes.foldl (step P O fuel) ⟨0, 1⟩).p := rfl

/-- The algorithm starts from `X = ∅`, `p = 1` (line 22). -/
@[simp]
theorem run_nil (fuel : ℕ) : run P O fuel ([] : List ι) = 0 := by
  simp [run]

end Ttc
