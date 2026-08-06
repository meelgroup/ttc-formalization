/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Convex.Basic
import Ttc.Model.Prelude

/-!
# `thm:decomposition` and the convexity of a cube's region

The proof content behind `Model/ProblemSetting`. Two groups:

* **The two inclusions of `thm:decomposition`** — soundness `P(cᵢ) ⊆ Sol(F)`
  (`Ttc.region_subset_sol`) and completeness `Sol(F) ⊆ ⋃ᵢ P(cᵢ)`
  (`Ttc.sol_subset_iUnion_region`). The paper keeps that split, and so do we;
  `Model/ProblemSetting` combines them into `Ttc.sol_eq_iUnion_region`.
* **Convexity of a cube's region** (`Ttc.convex_region`), substantiating the
  paper's claim that each cube denotes a convex polytope — with the caveat that
  it need not be *closed*, since a negated atom contributes a strict inequality.

**This module is fully proved: no hypotheses beyond `Ttc.IsDNFOf`.**
-/

namespace Ttc

open Set

variable {A X : Type*} {n : ℕ} {M : A → Set X} {φ : BForm A} {D : DNF A}

/-! ## Regions as intersections -/

/-- A cube's region is the intersection of the sets denoted by its literals. -/
theorem region_eq_iInter (c : Cube A) :
    region M c = ⋂ l ∈ c, litSet M l := by
  ext x
  simp only [mem_region_iff, mem_iInter]
  refine forall_congr' fun l => forall_congr' fun _ => ?_
  cases hb : l.pos <;> simp [Lit.holds, litSet, hb, induced]

/-! ## Convexity of a cube's region

The paper asserts that each cube denotes a *convex polytope*. With linear atoms
this is true for convexity, but a negated atom contributes the **open** half-space
`{x | b < ⟪a,x⟫}`, so the region is in general not closed. See below.
-/

/-- Each `litSet` of a linear atom system is convex: a positive literal gives a
closed half-space, a negative literal the complementary **open** half-space.

This substantiates the paper's claim that `P(c)` is convex. Note that it is *not*
in general a polytope in the standard (closed, `Ax ≤ b`) sense: negative literals
contribute strict inequalities. -/
theorem convex_litSet (atoms : A → LinAtom n) (l : Lit A) :
    Convex ℝ (litSet (fun a => (atoms a).halfspace) l) := by
  have hlin : IsLinearMap ℝ (fun x : Space n => ∑ i, (atoms l.atom).coeff i * x i) := by
    constructor
    · intro x y
      simp only [PiLp.add_apply, mul_add]
      exact Finset.sum_add_distrib
    · intro c x
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  cases hb : l.pos
  · have : (litSet (fun a => (atoms a).halfspace) l) =
        {x : Space n | (atoms l.atom).bound < ∑ i, (atoms l.atom).coeff i * x i} := by
      ext x; simp [litSet, hb, LinAtom.halfspace, not_le]
    rw [this]
    exact convex_halfSpace_gt hlin _
  · have : (litSet (fun a => (atoms a).halfspace) l) =
        {x : Space n | ∑ i, (atoms l.atom).coeff i * x i ≤ (atoms l.atom).bound} := by
      ext x; simp [litSet, hb, LinAtom.halfspace]
    rw [this]
    exact convex_halfSpace_le hlin _

/-- The region of a cube over linear atoms is convex. -/
theorem convex_region (atoms : A → LinAtom n) (c : Cube A) :
    Convex ℝ (region (fun a => (atoms a).halfspace) c) := by
  rw [region_eq_iInter]
  exact convex_iInter fun l => convex_iInter fun _ => convex_litSet atoms l

/-! ## The two inclusions of `thm:decomposition`

Formalisation of `thm:decomposition` of *Efficient Volume Computation
for SMT Formulas*:

> Let `F_dnf = ⋁_{i=1}^m c_i` be the DNF abstraction of the SMT formula `F`. Then
> `⋃_{i=1}^m P(c_i) = Sol(F)`.

The paper splits the argument into *soundness* (`P(c_i) ⊆ Sol(F)`) and
*completeness* (`Sol(F) ⊆ ⋃ P(c_i)`); we keep that split and combine them in
`Model/ProblemSetting` (`Ttc.sol_eq_iUnion_region`).
-/

/-- **Soundness of each cube.** Every cube of a DNF representation of `φ` denotes a
region contained in the solution set of `φ`. -/
theorem region_subset_sol (h : IsDNFOf D φ) {c : Cube A} (hc : c ∈ D) :
    region M c ⊆ sol M φ := by
  intro x hx
  exact (h (induced M x)).1 ⟨c, hc, hx⟩

/-- **Completeness of the union.** Every solution of `φ` lies in the region of some
cube of a DNF representation of `φ`. -/
theorem sol_subset_iUnion_region (h : IsDNFOf D φ) :
    sol M φ ⊆ ⋃ c ∈ D, region M c := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := (h (induced M x)).2 hx
  exact mem_biUnion hc hxc

/-- **`thm:decomposition`.** The union of the regions of a DNF abstraction's cubes
is exactly `Sol(F)`. This is what makes the set the algorithm enumerates and the
set `thm:volumettc` bounds the same set. -/
theorem sol_eq_iUnion_region (h : IsDNFOf D φ) :
    ⋃ c ∈ D, region M c = sol M φ :=
  Subset.antisymm
    (iUnion₂_subset fun _ hc => region_subset_sol h hc)
    (sol_subset_iUnion_region h)

end Ttc
