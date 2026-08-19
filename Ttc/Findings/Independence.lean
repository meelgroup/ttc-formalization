/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CubeBounds
import Ttc.Exec.Inputs

/-!
# `hφ` and `hbdd` are logically independent

**Verdict: neither of `Ttc.ttc_volume`'s two conditions on the input
formula implies the other, and this file machine-checks both directions.**

`Ttc.ttc_volume` (`Model/Theorem.lean`) takes

```
(hφ   : φ.IsPositive)                                 -- no negation occurs in φ
(hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))  -- Sol(F) is bounded
```

and it is natural to ask whether one is redundant.  It is not, in either
direction:

* `Ttc.Independence.exists_isBounded_not_isPositive` — a formula whose solution
  set is the interval `[-1, 1] ⊆ ℝ¹`, hence bounded, but which contains a
  negation.  So `hbdd` does not imply `hφ`.
* `Ttc.Independence.exists_isPositive_not_isBounded` — `Ttc.BForm.tt`, positive
  by definition, whose solution set is all of `ℝⁿ`.  So `hφ` does not imply
  `hbdd`.
* `Ttc.Independence.exists_isPositive_not_isBounded_halfspace` — the same, at a
  non-degenerate witness: the single positive atom `x₀ ≤ 0`, whose solution set
  is a genuine half-space (`≠ Set.univ`) and still unbounded.  `tt` is arguably
  a special case; this one is not.

## What each hypothesis is for

`hφ` is a **syntactic** condition on the formula: no negation occurs in it.  It
is needed because a negated atom denotes an *open* half-space, whereas the
lattice-counting side (`lem:nonconv`, `lem:lattice`) is stated for intersections
of *closed* half-spaces — README finding 5, and the docstring of
`Ttc.BForm.IsPositive` (`Model/Prelude.lean`).  It constrains the *shape of the
formula* and says nothing about the geometry of `Sol(F)`.

`hbdd` is a **semantic** condition on the solution set.  It is needed because
`Ttc.volSol` is an `ENNReal.toReal`, and `ENNReal.toReal ⊤ = 0`; an unbounded
`Sol(F)` therefore has `volSol = 0`, and the theorem would certify that the
output is approximately `0` — a true but useless statement about a body of
infinite volume (README finding 16).  That `hbdd` cannot simply be dropped is
already recorded, with a witness, in `Ttc.VolSolCheck.volSol_tt_eq_zero`
(`Volume/VolSolCheck.lean`); it is not redone here.  It constrains the *geometry*
and says nothing about the syntax of `φ`.

Different kinds of object are constrained, so it is unsurprising that neither
implies the other — but "unsurprising" is not "checked", and the two theorems
below are the check.  Neither binder can be dropped in favour of the other.

## Scope

These are independence witnesses, nothing more.  They do **not** claim that the
conjunction `hφ ∧ hbdd` is the weakest usable hypothesis pair, only that neither
conjunct is derivable from the other.
-/

namespace Ttc

namespace Independence

open Set

/-! ## Direction 1: bounded does not imply positive

The witness lives in `ℝ¹` over three atoms:

| atom | `coeff` | `bound` | half-space |
| --- | --- | --- | --- |
| `0` | `1` | `1` | `x ≤ 1` |
| `1` | `-1` | `1` | `-x ≤ 1`, i.e. `x ≥ -1` |
| `2` | `1` | `-5` | `x ≤ -5` |

and the formula is `a₀ ∧ (a₁ ∧ ¬a₂)`.  Its solution set is
`[-1, 1] ∩ {x | x > -5} = [-1, 1]`, which is bounded; the `¬` makes
`Ttc.BForm.IsPositive` reduce to `False`.  The third atom is there so that the
negation is not vacuous — dropping the negated conjunct would change the
solution set, so the formula is not "morally positive".
-/

/-- **The three atoms of the direction-1 witness.**  `boxAtoms 0` is `x ≤ 1`,
`boxAtoms 1` is `-x ≤ 1`, and `boxAtoms 2` is `x ≤ -5`. -/
def boxAtoms : Fin 3 → LinAtom 1 :=
  ![⟨fun _ => 1, 1⟩, ⟨fun _ => -1, 1⟩, ⟨fun _ => 1, -5⟩]

/-- **The direction-1 witness formula**, `a₀ ∧ (a₁ ∧ ¬a₂)`.  Bounded solution
set, one negation. -/
def boxForm : BForm (Fin 3) :=
  (BForm.atom 0).and ((BForm.atom 1).and ((BForm.atom 2).neg))

/-- `Ttc.Independence.boxForm` is not positive: `Ttc.BForm.IsPositive` sends
`.neg _` to `False`. -/
theorem not_isPositive_boxForm : ¬ boxForm.IsPositive := fun h => h.2.2

/-- The solution set of `Ttc.Independence.boxForm` sits inside the unit ball:
the first two atoms already pin `|x₀| ≤ 1`. -/
theorem sol_boxForm_subset_closedBall :
    sol (atomSet boxAtoms) boxForm ⊆ Metric.closedBall (0 : Space 1) 1 := by
  intro x hx
  simp only [mem_sol_iff, boxForm, BForm.holds] at hx
  obtain ⟨h1, h2, -⟩ := hx
  have e1 : ∑ i, (boxAtoms 0).coeff i * x i ≤ (boxAtoms 0).bound := h1
  have e2 : ∑ i, (boxAtoms 1).coeff i * x i ≤ (boxAtoms 1).bound := h2
  simp only [boxAtoms, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.sum_univ_one, one_mul, neg_mul] at e1 e2
  have hnorm : ‖x‖ = |x 0| := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs]
  simp only [Metric.mem_closedBall, dist_zero_right, hnorm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Bounded does not imply positive.**

There is an instance whose solution set `Sol(F)` is bounded — so `hbdd` holds —
but whose formula contains a negation, so `hφ` fails.  Hence `hbdd` does not
imply `hφ`, and `Ttc.ttc_volume`'s `hφ` cannot be dropped in favour of
`hbdd`.

The witness is `a₀ ∧ (a₁ ∧ ¬a₂)` over the three half-spaces `x ≤ 1`, `-x ≤ 1`,
`x ≤ -5` of `ℝ¹`; its solution set is the interval `[-1, 1]`. -/
theorem exists_isBounded_not_isPositive :
    ∃ (atoms : Fin 3 → LinAtom 1) (φ : BForm (Fin 3)),
      Bornology.IsBounded (sol (atomSet atoms) φ) ∧ ¬ φ.IsPositive :=
  ⟨boxAtoms, boxForm,
    Metric.isBounded_closedBall.subset sol_boxForm_subset_closedBall,
    not_isPositive_boxForm⟩

/-! ## Direction 2: positive does not imply bounded

Two witnesses.  The first is the empty conjunction `Ttc.BForm.tt`, which is
positive by definition and solved by every point; the second is a single
positive atom, whose solution set is a proper half-space and still unbounded.
-/

variable {A : Type*} {n : ℕ}

/-- `Ttc.BForm.tt` is solved by every point, for any interpretation. -/
theorem sol_tt (M : A → Set (Space n)) : sol M (BForm.tt : BForm A) = univ :=
  eq_univ_of_forall fun _ => trivial

/-- **Positive does not imply bounded.**

There is an instance whose formula is positive — so `hφ` holds — but whose
solution set is all of `ℝⁿ`, so `hbdd` fails.  Hence `hφ` does not imply `hbdd`,
and `Ttc.ttc_volume`'s `hbdd` cannot be dropped in favour of `hφ`.

The witness is `Ttc.BForm.tt`, the empty conjunction, at arbitrary atoms;
unboundedness of `Set.univ` is `Ttc.not_isBounded_univ_space`.  See
`Ttc.Independence.exists_isPositive_not_isBounded_halfspace` for a witness that
is not a degenerate formula. -/
theorem exists_isPositive_not_isBounded (hn : 1 ≤ n) :
    ∃ (atoms : A → LinAtom n) (φ : BForm A),
      φ.IsPositive ∧ ¬ Bornology.IsBounded (sol (atomSet atoms) φ) :=
  ⟨fun _ => ⟨0, 0⟩, BForm.tt, trivial, by
    rw [sol_tt]; exact not_isBounded_univ_space hn⟩

/-- **The atom `x₀ ≤ 0`** — the half-space witness for direction 2. -/
def rayAtom (n : ℕ) (hn : 1 ≤ n) : LinAtom n :=
  ⟨fun i => if i = ⟨0, hn⟩ then 1 else 0, 0⟩

/-- Along the `x₀`-axis, `Ttc.Independence.rayAtom`'s linear form is the
coordinate itself. -/
theorem rayAtom_sum (hn : 1 ≤ n) (c : ℝ) :
    ∑ i, (rayAtom n hn).coeff i * (EuclideanSpace.single (⟨0, hn⟩ : Fin n) c) i = c := by
  simp [rayAtom]

/-- Membership in the solution set of the single atom `x₀ ≤ 0`, at a point of the
`x₀`-axis. -/
theorem mem_sol_rayAtom (hn : 1 ≤ n) (a : A) {c : ℝ} (hc : c ≤ 0) :
    (EuclideanSpace.single (⟨0, hn⟩ : Fin n) c)
      ∈ sol (atomSet (fun _ : A => rayAtom n hn)) (BForm.atom a) := by
  have h : ∑ i, (rayAtom n hn).coeff i * (EuclideanSpace.single (⟨0, hn⟩ : Fin n) c) i
      ≤ (rayAtom n hn).bound := by rw [rayAtom_sum hn c]; exact hc
  exact h

/-- The half-space `x₀ ≤ 0` is a proper subset of `ℝⁿ`: the point `e₀` is not in
it. -/
theorem sol_rayAtom_ne_univ (hn : 1 ≤ n) (a : A) :
    sol (atomSet (fun _ : A => rayAtom n hn)) (BForm.atom a) ≠ univ := by
  intro h
  have hmem : (EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ))
      ∈ sol (atomSet (fun _ : A => rayAtom n hn)) (BForm.atom a) := h ▸ mem_univ _
  have h1 : ∑ i, (rayAtom n hn).coeff i * (EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)) i
      ≤ (rayAtom n hn).bound := hmem
  rw [rayAtom_sum hn 1] at h1
  have : (1 : ℝ) ≤ 0 := h1
  linarith

/-- The half-space `x₀ ≤ 0` is unbounded: it contains the whole negative
`x₀`-axis. -/
theorem not_isBounded_sol_rayAtom (hn : 1 ≤ n) (a : A) :
    ¬ Bornology.IsBounded (sol (atomSet (fun _ : A => rayAtom n hn)) (BForm.atom a)) := by
  intro hb
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Space n)).mp hb
  have hnn : (0 : ℝ) ≤ |r| + 1 := by positivity
  have hmem := hr (mem_sol_rayAtom hn a (c := -(|r| + 1)) (by linarith))
  rw [Metric.mem_closedBall, dist_zero_right, PiLp.norm_single, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg hnn] at hmem
  linarith [le_abs_self r]

/-- **Positive does not imply bounded, at a non-degenerate witness.**

Same conclusion as `Ttc.Independence.exists_isPositive_not_isBounded`, but the
formula is a single positive atom rather than the empty conjunction, and its
solution set is a genuine half-space — `≠ Set.univ` — that happens to be
unbounded.  So the failure of `hbdd` under `hφ` is not an artefact of a
degenerate formula.

The witness is the atom `x₀ ≤ 0` of `ℝⁿ`, assigned to every index. -/
theorem exists_isPositive_not_isBounded_halfspace (hn : 1 ≤ n) (a : A) :
    ∃ (atoms : A → LinAtom n) (φ : BForm A),
      φ.IsPositive ∧ sol (atomSet atoms) φ ≠ univ ∧
        ¬ Bornology.IsBounded (sol (atomSet atoms) φ) :=
  ⟨fun _ => rayAtom n hn, BForm.atom a, trivial,
    sol_rayAtom_ne_univ hn a, not_isBounded_sol_rayAtom hn a⟩

end Independence

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.Independence.exists_isBounded_not_isPositive
#print axioms Ttc.Independence.exists_isPositive_not_isBounded
#print axioms Ttc.Independence.exists_isPositive_not_isBounded_halfspace
