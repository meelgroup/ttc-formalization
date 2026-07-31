/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Decomposition
import Ttc.Analysis.Geometry

/-!
# The facet system of a DNF over linear atoms

`Ttc.FacetSystem` is the input to the whole `lem:nonconv` chain, but nothing so
far ever *builds* one — every theorem there is stated over free reals. This file
constructs the facet system of an actual DNF, so that `Q = ⋃ᵢ P(cᵢ)` is literally
`Ttc.FacetSystem.body 0` and `Q = Sol(F)` (`Ttc.body_eq_sol`).

## Scope: positive literals only

A `Ttc.FacetSystem.piece` is an intersection of **closed** half-spaces
`f j x ≤ b j`. A *negated* atom denotes the **open** half-space `{x | b < ⟪a,x⟫}`,
so a cube containing one cannot be a `piece` — the construction below is therefore
restricted to DNFs whose literals are all positive (`Ttc.DNF.IsPositive`).

This is not a technicality that volume arguments wash out. The README's finding 5
notes that a cube's region is convex but not closed, and that volumes agree
because the boundary is null. That is right for the *volume* side — but
`lem:nonconv` and `lem:lattice` also count **lattice points**, and the boundary is
exactly where a set and its closure differ for counting. In one dimension, the
atom `x ≤ 0` negated gives `{x | 0 < x}`, whose closure gains the lattice point
`0`; on the fine lattice `𝕃ⁿ = 10^(−ρ)·ℤⁿ` a facet hyperplane can carry many such
points. So replacing regions by their closures is *not* free on the count side,
and we take the restriction rather than hide the difference.
-/

namespace Ttc

open Set

variable {A : Type*} {n : ℕ}

/-- A cube is **positive** when none of its literals is negated. -/
def Cube.IsPositive (c : Cube A) : Prop := ∀ l ∈ c, l.pos = true

/-- A DNF is **positive** when all of its cubes are. -/
def DNF.IsPositive (D : DNF A) : Prop := ∀ c ∈ D, Cube.IsPositive c

/-- The linear form `x ↦ ∑ₖ Aₖ xₖ` of a linear atom, bundled. -/
noncomputable def LinAtom.form (a : LinAtom n) : Space n →ₗ[ℝ] ℝ :=
  IsLinearMap.mk' (fun x => ∑ k, a.coeff k * x k) <| by
    constructor
    · intro x y
      simp only [PiLp.add_apply, mul_add]
      exact Finset.sum_add_distrib
    · intro c x
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem LinAtom.form_apply (a : LinAtom n) (x : Space n) :
    a.form x = ∑ k, a.coeff k * x k := rfl

/-- Facets of a DNF: one per literal of each of its cubes. -/
abbrev FacetIndex (D : DNF A) := Σ c : {c : Cube A // c ∈ D}, {l : Lit A // l ∈ c.val}

/-- **The facet system of a DNF over linear atoms.** Polytopes are indexed by the
cubes of `D`; the facets of cube `c` are its literals, each contributing
`⟪coeff, x⟫ ≤ bound` with weight `‖coeff‖`. -/
noncomputable def facetSystem (atoms : A → LinAtom n) (D : DNF A) :
    FacetSystem n {c : Cube A // c ∈ D} (FacetIndex D) where
  part := fun j => j.1
  f := fun j => (atoms j.2.val.atom).form
  b := fun j => (atoms j.2.val.atom).bound
  w := fun j => Real.sqrt (∑ k, (atoms j.2.val.atom).coeff k ^ 2)
  w_nonneg := fun _ => Real.sqrt_nonneg _

/-- **Each cube's region is the corresponding piece**, for a positive cube. This
is the identification the `lem:nonconv` chain was missing. -/
theorem region_eq_piece (atoms : A → LinAtom n) {D : DNF A} (hD : DNF.IsPositive D)
    (i : {c : Cube A // c ∈ D}) :
    region (fun a => (atoms a).halfspace) i.val = (facetSystem atoms D).piece 0 i := by
  ext x
  simp only [mem_region_iff, FacetSystem.mem_piece, facetSystem, zero_mul, add_zero,
    LinAtom.form_apply]
  constructor
  · intro hx j hj
    obtain ⟨c', l⟩ := j
    cases hj
    have hl := hx l.val l.property
    rw [Lit.holds, hD c'.val c'.property l.val l.property] at hl
    simpa [LinAtom.halfspace, induced] using hl
  · intro hx l hl
    have h := hx ⟨i, ⟨l, hl⟩⟩ rfl
    rw [Lit.holds, hD i.val i.property l hl]
    simpa [LinAtom.halfspace, induced] using h

/-- **`Q` is `Sol(F)`.** The union of the facet system's pieces is exactly the
solution set of the formula — combining `Ttc.region_eq_piece` with
`thm:decomposition`. This is what makes `lem:nonconv`'s `Q` the real object. -/
theorem body_eq_sol (atoms : A → LinAtom n) {D : DNF A} {φ : BForm A}
    (hD : DNF.IsPositive D) (hDNF : IsDNFOf D φ) :
    (facetSystem atoms D).body 0 = sol (fun a => (atoms a).halfspace) φ := by
  rw [FacetSystem.body]
  have hpiece : ∀ i : {c : Cube A // c ∈ D},
      (facetSystem atoms D).piece 0 i = region (fun a => (atoms a).halfspace) i.val :=
    fun i => (region_eq_piece atoms hD i).symm
  calc ⋃ i, (facetSystem atoms D).piece 0 i
      = ⋃ i : {c : Cube A // c ∈ D}, region (fun a => (atoms a).halfspace) i.val := by
        exact iUnion_congr hpiece
    _ = ⋃ c ∈ D, region (fun a => (atoms a).halfspace) c := by
        rw [← Set.iUnion_subtype (fun c => c ∈ D)
          (fun c => region (fun a => (atoms a).halfspace) c.val)]
    _ = sol (fun a => (atoms a).halfspace) φ := sol_eq_iUnion_region hDNF

/-! ## The geometric covering of `claim:cl`

A point that escapes the inflated body while `x` sits in the body must cross some
facet — the paper's step "for `x ∈ Q` and `p ∈ C(x) ∖ Q'` we have
`A_ij·(p − x) ≥ κ‖A_ij‖`". This is the `hcover` hypothesis of
`Ttc.prodKernel_escape_bound`, and it is elementary.
-/

/-- **The facet-crossing.** If `x` lies in the body and `p` outside its inflation,
some facet `j` has `κ·w j ≤ f j p − f j x`. -/
theorem cover_of_notMem_body {n : ℕ} {ι F : Type*} (S : FacetSystem n ι F) {κ : ℝ}
    {x p : Space n} (hx : x ∈ S.body 0) (hp : p ∉ S.body κ) :
    ∃ j, κ * S.w j ≤ S.f j p - S.f j x := by
  obtain ⟨i, hi⟩ := S.mem_body.1 hx
  have hpi : p ∉ S.piece κ i := fun h => hp (S.mem_body.2 ⟨i, h⟩)
  simp only [FacetSystem.mem_piece, not_forall] at hpi
  obtain ⟨j, hpart, hlt⟩ := hpi
  have hxj : S.f j x ≤ S.b j := by have := hi j hpart; simpa using this
  push Not at hlt
  exact ⟨j, by linarith⟩

/-- **The covering, as a union over facets.** -/
theorem diff_body_subset_cover {n : ℕ} {ι F : Type*} [Fintype F] (S : FacetSystem n ι F)
    {κ : ℝ} {x : Space n} (hx : x ∈ S.body 0) (C : Set (Space n)) :
    C \ S.body κ ⊆ ⋃ j ∈ (Finset.univ : Finset F), {p | κ * S.w j ≤ S.f j p - S.f j x} := by
  intro p hp
  obtain ⟨j, hj⟩ := cover_of_notMem_body S hx hp.2
  exact Set.mem_biUnion (Finset.mem_univ j) hj

end Ttc
