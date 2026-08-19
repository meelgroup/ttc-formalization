/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Ttc.Exec.Params
import Ttc.Model.Pseudocode

/-!
# The inscribed ball, constructed rather than supplied

The headline used to carry, at the rung this file was written for, **four** binders
for the inscribed ball that `alg:prec` line 86 obtains from an LP,
`γ̂ ← MaxInscribedBall(Pⁱ)`:

```
(cen : {c : Cube A // c ∈ toDNFd φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
(ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region (atomSet atoms) i.val)
```

This file replaces all four by a *construction* — `Ttc.cenOf` and `Ttc.gammaOf` — plus
**one** condition on the input, `hint`, one clause per cube of the DNF.

## What this is, and what it is not

This is **not** an LP with an optimality proof, and nothing here claims to compute the
*maximum* inscribed ball. `Ttc.ballData` picks, classically, *some* ball contained in a
cube's region — the choice is `Exists.choose` on the statement "a ball of positive
radius fits" — and `Ttc.gammaOf` takes the least of the resulting radii over the cubes
(the paper's shared `γ̂`; the worst ratio `γ/γ̂ᵢ` is the ratio at the least `γ̂ᵢ`).

Non-maximality costs nothing in soundness. The radius enters the algorithm only through
the precision `ρ = ⌈log₁₀(γ/γ̂)⌉`, and a smaller `γ̂` only makes `ρ` **larger**: a finer
lattice, hence a more expensive but still correct run. So the guarantee that
`ttc_volume` states is untouched; only the efficiency is looser than what
`alg:prec` line 86 would deliver.

## What is unconditional and what is not

* `Ttc.ball_subset_cenOf` — the replacement for `ball_subset` — is **unconditional**.
  When a cube's region contains no ball at all (it is empty, or lower-dimensional), the
  constructed radius is `0`, `Metric.ball _ 0 = ∅`, and the containment holds trivially.
* `Ttc.gammaOf_pos` — the replacement for `hgammaHat` — needs `hint`, and `hint` is a
  **genuine restriction on the input**, not bookkeeping: a DNF cube can be empty (two
  contradictory literals) or lower-dimensional (an equality-like conjunction), and then
  no positive-radius ball fits and `γ̂ = 0`. The paper's LP is infeasible in exactly the
  same situations. `Ttc.gammaOf_pos_of_interior` restates the condition in the form a
  reader can actually check: every cube's region has nonempty interior.
-/

namespace Ttc

variable {A : Type*} {n : ℕ}

/-! ## The per-cube ball

`Ttc.ballData` — line A8 of the preprocessing — is **defined in `Model/Pseudocode`**,
with the rest of the amended algorithm's vocabulary; only its theory is here. -/

/-- **Soundness, unconditional.** Either the choice gives a genuine inscribed ball, or
the radius is `0` and the ball is empty — either way it sits inside the region. -/
theorem ball_ballData_subset (M : A → Set (Space n)) (i : Cube A) :
    Metric.ball (ballData M i).1 (ballData M i).2 ⊆ region M i := by
  unfold ballData
  split
  · rename_i h
    exact h.choose_spec.2
  · simp

/-- The radius is positive exactly when the region contains *some* ball. -/
theorem ballData_snd_pos (M : A → Set (Space n)) {i : Cube A}
    (h : ∃ p : Space n × ℝ, 0 < p.2 ∧ Metric.ball p.1 p.2 ⊆ region M i) :
    0 < (ballData M i).2 := by
  unfold ballData
  rw [dif_pos h]
  exact h.choose_spec.1

/-- The radius is never negative: it is either a genuine positive radius or `0`. -/
theorem ballData_snd_nonneg (M : A → Set (Space n)) (i : Cube A) : 0 ≤ (ballData M i).2 := by
  unfold ballData
  split
  · rename_i h; exact h.choose_spec.1.le
  · exact le_refl 0

/-! ## The shared radius: the least of the per-cube radii

`Ttc.cenOf` and `Ttc.gammaOf` — lines A8 and A9 of the preprocessing — are
**defined in `Model/Pseudocode`**; only their theory is here. `Ttc.cenOf` is the
replacement for the headline's `cen` binder, `Ttc.gammaOf` for `gammaHat`. -/

/-- The per-cube radii are bounded below by `0`, so the infimum defining `gammaOf` is a
genuine greatest lower bound rather than the junk value of an unbounded family. -/
theorem bddBelow_ballData_snd (M : A → Set (Space n)) (D : DNF A) :
    BddBelow (Set.range fun i : {c : Cube A // c ∈ D} => (ballData M i.val).2) := by
  refine ⟨0, ?_⟩
  rintro x ⟨i, rfl⟩
  exact ballData_snd_nonneg M i.val

/-- The shared radius is at most each cube's own radius. -/
theorem gammaOf_le (M : A → Set (Space n)) (D : DNF A) (i : {c : Cube A // c ∈ D}) :
    gammaOf M D ≤ (ballData M i.val).2 :=
  ciInf_le (bddBelow_ballData_snd M D) i

/-- The shared radius is never negative. -/
theorem gammaOf_nonneg (M : A → Set (Space n)) (D : DNF A) : 0 ≤ gammaOf M D := by
  by_cases h : Nonempty {c : Cube A // c ∈ D}
  · haveI := h
    exact le_ciInf fun i => ballData_snd_nonneg M i.val
  · simp [gammaOf, not_nonempty_iff.mp h, Real.iInf_of_isEmpty]

/-- **`ball_subset`, discharged.** Unconditional — no hypothesis at all.

If cube `i`'s region contains no ball, `gammaOf M D ≤ (ballData M i.val).2 = 0`, the ball
on the left is empty, and the containment is vacuous. -/
theorem ball_subset_cenOf (M : A → Set (Space n)) (D : DNF A) (i : {c : Cube A // c ∈ D}) :
    Metric.ball (cenOf M D i) (gammaOf M D) ⊆ region M i.val :=
  (Metric.ball_subset_ball (gammaOf_le M D i)).trans (ball_ballData_subset M i.val)

/-- **`hgammaHat`, from one condition on the input.**

`hne` says the DNF has a cube — without it the index type is empty and `γ̂ = 0`. `hint`
says every cube's region admits *some* ball of positive radius; this is the honest
content of `alg:prec` line 86's LP being feasible. -/
theorem gammaOf_pos (M : A → Set (Space n)) {D : DNF A} (hne : D ≠ [])
    (hint : ∀ i : {c : Cube A // c ∈ D},
      ∃ p : Space n × ℝ, 0 < p.2 ∧ Metric.ball p.1 p.2 ⊆ region M i.val) :
    0 < gammaOf M D := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil D hne
  haveI : Nonempty {c : Cube A // c ∈ D} := ⟨⟨c, hc⟩⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min fun i : {c : Cube A // c ∈ D} => (ballData M i.val).2
  have hEq : gammaOf M D = (ballData M i₀.val).2 :=
    le_antisymm (gammaOf_le M D i₀) (le_ciInf hi₀)
  rw [hEq]
  exact ballData_snd_pos M (hint i₀)

/-! ## The readable form of the input condition

`hint` is phrased with an existential over `(centre, radius)` pairs because that is what
`ballData` chooses from. The condition a reader checks is the geometric one: the cube's
region has interior. -/

/-- A region with nonempty interior contains a ball of positive radius. -/
theorem exists_ball_of_interior_nonempty {M : A → Set (Space n)} {i : Cube A}
    (h : (interior (region M i)).Nonempty) :
    ∃ p : Space n × ℝ, 0 < p.2 ∧ Metric.ball p.1 p.2 ⊆ region M i := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  exact ⟨(x, r), hr, hsub⟩

/-- **`hgammaHat`, from the condition a reader can check.** The DNF has a cube, and every
cube's region has nonempty interior. -/
theorem gammaOf_pos_of_interior (M : A → Set (Space n)) {D : DNF A} (hne : D ≠ [])
    (hint : ∀ i : {c : Cube A // c ∈ D}, (interior (region M i.val)).Nonempty) :
    0 < gammaOf M D :=
  gammaOf_pos M hne fun i => exists_ball_of_interior_nonempty (hint i)

/-! ## Axiom profile -/

#print axioms ballData
#print axioms ball_ballData_subset
#print axioms ballData_snd_pos
#print axioms ballData_snd_nonneg
#print axioms cenOf
#print axioms gammaOf
#print axioms bddBelow_ballData_snd
#print axioms gammaOf_le
#print axioms gammaOf_nonneg
#print axioms ball_subset_cenOf
#print axioms gammaOf_pos
#print axioms exists_ball_of_interior_nonempty
#print axioms gammaOf_pos_of_interior

end Ttc
