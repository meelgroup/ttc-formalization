/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Pseudocode

/-!
# Structural invariants of the modelled execution

The algorithm-shaped facts about `Model/Pseudocode` — what the loop does to `X`
and `p` — and nothing else:

* the coverage filter only removes points (`Ttc.card_dropCovered_le`);
* `p` never increases and stays nonnegative, through both loops
  (`Ttc.halveDown_p`, `Ttc.absorb_p`);
* a state whose guard already fails is a fixpoint (`Ttc.absorb_of_settled`,
  `Ttc.halveDown_of_settled`);
* the output is `|X|/p` of the final state (`Ttc.run_eq`), by definition.

The *distributional* facts — that the output concentrates around
`|Q ∩ 𝕃ⁿ|/10^(ρn)` — are `lem:numlattice`, which this development assumes.

**Termination is deliberately not claimed.** Both `while` loops run on fuel. The
real second loop terminates because repeated thinning eventually brings
`Nᵢ + |X|` under `Thresh` *with high probability*; there is no deterministic
bound, so no fuel-independent termination theorem is available — and asserting
one would be false. What is recorded instead is that a state already satisfying
the guard is a fixpoint (`Ttc.absorb_of_settled`).
-/

namespace Ttc

open Multiset

variable {n : ℕ} {ι : Type*} (P : Params) (O : Oracles n ι)

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
theorem card_step_le (fuel : ℕ) (ρ : ℤ) (st : SketchState n) (i : ι) :
    card (step P O fuel ρ st i).X ≤
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
theorem run_eq (fuel : ℕ) (ρ : ℤ) (cubes : List ι) :
    run P O fuel ρ cubes =
      (card (cubes.foldl (step P O fuel ρ) ⟨0, 1⟩).X : ℝ) /
        (cubes.foldl (step P O fuel ρ) ⟨0, 1⟩).p := rfl

/-- The algorithm starts from `X = ∅`, `p = 1` (line 22). -/
@[simp]
theorem run_nil (fuel : ℕ) (ρ : ℤ) : run P O fuel ρ ([] : List ι) = 0 := by
  simp [run]

end Ttc
