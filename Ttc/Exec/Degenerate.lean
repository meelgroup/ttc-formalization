/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Ttc.Exec.Inscribed
import Ttc.Exec.Inputs
import Ttc.Exec.Geometry

/-!
# `hint` cannot be discharged: the degenerate cubes of a DNF

**Verdict: `Ttc.ttc_volume_estimate`'s `hint` — every polytope of the decomposition is
full-dimensional — is *not* dischargeable, and cannot be removed without restating
`thm:decomposition` up to null sets.**  This file proves the verdict rather than
asserting it: it lands the measure-theoretic half of the argument (dropping the
degenerate cubes is invisible to `Ttc.volSol`), and then an explicit input on which
every other hypothesis of `Ttc.ttc_volume_estimate` holds, `Ttc.volSol` is *positive*,
`hint` fails, and the repair that the measure-theoretic half suggests provably destroys
`Ttc.IsDNFOf`.

## The shape of the argument

A cube of `Ttc.toDNFd φ` can be degenerate in two ways.  Its region can be **empty**
(two contradictory literals) — such a cube contributes nothing to `⋃ᵢ P(cᵢ)` and can be
deleted with `Ttc.IsDNFOf` intact.  Or its region can be **nonempty but
lower-dimensional** — an equality-like conjunction such as `x ≤ 0 ∧ −x ≤ 0`.  That is
the hard case, and it is the one this file is about.

1. **A degenerate region is null.**  `Ttc.region` over linear atoms is convex
   (`Ttc.convex_region`), and a convex set with empty interior has Lebesgue measure
   zero.  Mathlib has no lemma under that name; the route is
   `Convex.interior_nonempty_iff_affineSpan_eq_top` together with
   `MeasureTheory.Measure.addHaar_affineSubspace`, which this development already
   packages as `Ttc.interior_nonempty_of_measure_ne_zero` (`Exec/Geometry`).  Its
   contrapositive is `Ttc.volume_region_eq_zero_of_interior_empty`.  Note that no
   positivity hypothesis on the cube is needed: `Ttc.convex_region` is unconditional,
   because a *negative* literal contributes an open half-space, which is convex too.

2. **Dropping the degenerate cubes preserves `Vol(F)` exactly.**
   `Ttc.nondegenCubes` is the sublist of cubes whose region has nonempty interior, and
   `Ttc.volume_biUnion_nondegenCubes` says the two finite unions have the *same*
   Lebesgue measure — the difference is a finite union of null sets.  Composed with
   `thm:decomposition` this gives `Ttc.volSol_eq_toReal_biUnion_nondegenCubes`: the
   quantity the theorem's conclusion is about does not see the deletion.

3. **But `Ttc.IsDNFOf` does see it.**  `Ttc.IsDNFOf D φ` is a statement about *Boolean
   assignments*, not about points of `ℝⁿ`: `∀ v : A → Prop, D.holds v ↔ φ.holds v`.
   Deleting a cube deletes a satisfying assignment class, and that is fatal even when
   the deleted cube's region was already contained in the union of the others.
   `Ttc.not_isDNFOf_nondegenCubes_degForm` exhibits this.

So the repair suggested by (2) is unavailable: everything downstream of
`Ttc.sol_eq_iUnion_region` — `Ttc.latticeCount`, `lem:lattice`, `Lattice/Assembled` —
is stated over `Ttc.sol` and `Ttc.IsDNFOf`, not over `Ttc.volSol`.

## Why `hint` is needed cube-by-cube, not just for one cube

`Ttc.gammaOf` is the *infimum* of the per-cube radii (`Exec/Inscribed`), so a single
degenerate cube sends `γ̂` to `0` and `ρ = ⌈log₁₀(γ/γ̂)⌉` to a junk value.  This is not
an artefact of taking a minimum: `ball_subset` is consumed per cube downstream
(`Ttc.TtcProb.ball_subset` at `Lattice/PerCube`, and at `Sampler/Bridge` where it is
what makes `Vol(P(cᵢ)) > 0` so that the ball walk inside cube `i` has a target to
sample from).  The algorithm walks inside *every* cube of the decomposition, so a
weakening of `hint` to "some cube is full-dimensional" — which is equivalent to
`0 < Vol(F)` — is not available either.

## The counterexample

`Ttc.degForm` is `(x ≤ 0 ∧ −x ≤ 0) ∨ (x ≤ 1 ∧ −x ≤ 1)` in dimension `1`.  Its DNF has
two cubes: `Ttc.thinCube`, whose region is the single point `0`, and `Ttc.fatCube`,
whose region is `[−1, 1]`.  The formula is negation-free, its solution set is bounded,
no atom has a zero normal, and `Vol(F) > 0` (`Ttc.volSol_degForm_pos`; the value is
`2`, but only positivity is proved, since only positivity is what matters) — so the
conclusion of `Ttc.ttc_volume_estimate` is not vacuous for it.  Yet `hint` fails
(`Ttc.hint_not_derivable`), and the deletion of `Ttc.thinCube` — which changes the
solution *set* not at all, since `{0} ⊆ [−1, 1]` — still destroys `Ttc.IsDNFOf`.

## What would be needed to finish the job

Exactly one thing, and it is a large refactor deliberately not attempted here: a
version of `thm:decomposition` up to null sets, i.e. `Ttc.sol M φ =ᵐ[volume] ⋃ c ∈ D', region M c`
for the pruned list `D'`, together with a re-derivation of `Ttc.latticeCount` and
`lem:lattice` from that weaker statement.  `lem:lattice` counts *lattice points* of
`Ttc.sol`, and lattice points are a null set, so an almost-everywhere decomposition
gives no control over the count at all — the lattice-side argument would have to be
rebuilt from the pruned union directly rather than from `Ttc.sol`.  Until that is done,
`hint` is a genuine condition on the input, exactly as `alg:prec` line 86's LP being
feasible is a condition on the input.
-/

namespace Ttc

open MeasureTheory Set

variable {A : Type*} {n : ℕ}

/-! ## 1. A degenerate region is null -/

/-- **A convex subset of `ℝⁿ` with empty interior has Lebesgue measure zero.**  The
contrapositive of `Ttc.interior_nonempty_of_measure_ne_zero`; Mathlib has no lemma of
this name, the content being `Convex.interior_nonempty_iff_affineSpan_eq_top` plus
`MeasureTheory.Measure.addHaar_affineSubspace`. -/
theorem volume_eq_zero_of_interior_eq_empty {S : Set (Space n)} (hc : Convex ℝ S)
    (h : interior S = ∅) : volume S = 0 := by
  by_contra h0
  exact (interior_nonempty_of_measure_ne_zero hc h0).ne_empty h

/-- **A lower-dimensional cube contributes nothing to the volume.**

No hypothesis on the cube is needed — in particular not `Ttc.Cube.IsPositive` — because
`Ttc.convex_region` is unconditional: a negated literal denotes an *open* half-space,
which is still convex. -/
theorem volume_region_eq_zero_of_interior_empty (M : A → Set (Space n))
    {atoms : A → LinAtom n} (hM : M = atomSet atoms) {c : Cube A}
    (h : interior (region M c) = ∅) : volume (region M c) = 0 := by
  subst hM
  exact volume_eq_zero_of_interior_eq_empty (convex_region atoms c) h

/-! ## 2. Dropping the degenerate cubes preserves the volume

`Ttc.nondegenCubes` — line A2 of the preprocessing, defined in `Model/Pseudocode` —
keeps exactly the cubes whose region has nonempty interior, the cubes `hint` is
about.  The choice is classical (having nonempty interior is not decidable), hence
its `noncomputable`.  Everything proved about it is here. -/

@[simp]
theorem mem_nondegenCubes {M : A → Set (Space n)} {D : DNF A} {c : Cube A} :
    c ∈ nondegenCubes M D ↔ c ∈ D ∧ (interior (region M c)).Nonempty := by
  simp only [nondegenCubes, List.mem_filter, decide_eq_true_eq]

/-- `Ttc.nondegenCubes` only removes cubes. -/
theorem nondegenCubes_subset {M : A → Set (Space n)} {D : DNF A} {c : Cube A}
    (h : c ∈ nondegenCubes M D) : c ∈ D := (mem_nondegenCubes.1 h).1

/-- **The finite union is unchanged, as a measure.**  The cubes deleted by
`Ttc.nondegenCubes` have null regions, and there are finitely many of them. -/
theorem volume_biUnion_nondegenCubes (atoms : A → LinAtom n) (D : DNF A) :
    volume (⋃ c ∈ D, region (atomSet atoms) c)
      = volume (⋃ c ∈ nondegenCubes (atomSet atoms) D, region (atomSet atoms) c) := by
  set M := atomSet atoms with hM
  set G : Set (Cube A) := {c | c ∈ nondegenCubes M D} with hG
  set B : Set (Cube A) := {c | c ∈ D ∧ ¬ (interior (region M c)).Nonempty} with hB
  have hsplit : {c : Cube A | c ∈ D} = G ∪ B := by
    ext c
    simp only [hG, hB, Set.mem_setOf_eq, Set.mem_union, mem_nondegenCubes]
    tauto
  have hBnull : volume (⋃ c ∈ B, region M c) = 0 := by
    refine (measure_biUnion_null_iff ?_).2 ?_
    · exact ((List.finite_toSet D).subset fun c hc => hc.1).countable
    · rintro c ⟨-, hcE⟩
      exact volume_region_eq_zero_of_interior_empty M hM (Set.not_nonempty_iff_eq_empty.1 hcE)
  have hunion : (⋃ c ∈ D, region M c) = (⋃ c ∈ G, region M c) ∪ ⋃ c ∈ B, region M c := by
    rw [show (⋃ c ∈ D, region M c) = ⋃ c ∈ ({c | c ∈ D} : Set (Cube A)), region M c from rfl,
      hsplit, Set.biUnion_union]
  rw [hunion]
  refine le_antisymm ?_ (measure_mono Set.subset_union_left)
  calc volume ((⋃ c ∈ G, region M c) ∪ ⋃ c ∈ B, region M c)
      ≤ volume (⋃ c ∈ G, region M c) + volume (⋃ c ∈ B, region M c) := measure_union_le _ _
    _ = volume (⋃ c ∈ G, region M c) := by rw [hBnull, add_zero]

/-- **`Vol(F)` does not see the deletion.**  `thm:decomposition`
(`Ttc.sol_eq_iUnion_region`) turns `Ttc.volume_biUnion_nondegenCubes` into a statement
about `Ttc.sol` itself. -/
theorem volume_sol_eq_volume_biUnion_nondegenCubes (atoms : A → LinAtom n) {φ : BForm A}
    {D : DNF A} (hD : IsDNFOf D φ) :
    volume (sol (atomSet atoms) φ)
      = volume (⋃ c ∈ nondegenCubes (atomSet atoms) D, region (atomSet atoms) c) := by
  rw [← sol_eq_iUnion_region hD]
  exact volume_biUnion_nondegenCubes atoms D

/-- **`Ttc.volSol`, the quantity `thm:volumettc` is about, is invariant under dropping
the degenerate cubes.**  This is the whole of the "it should be dischargeable" case —
and it is not enough, because `Ttc.IsDNFOf` is not invariant; see
`Ttc.not_isDNFOf_nondegenCubes_degForm`. -/
theorem volSol_eq_toReal_biUnion_nondegenCubes (atoms : A → LinAtom n) {φ : BForm A}
    {D : DNF A} (hD : IsDNFOf D φ) :
    volSol (atomSet atoms) φ
      = (volume (⋃ c ∈ nondegenCubes (atomSet atoms) D, region (atomSet atoms) c)).toReal := by
  rw [volSol, volume_sol_eq_volume_biUnion_nondegenCubes atoms hD]

/-! ## 3. The counterexample

Dimension `1`, four atoms, `F = (x ≤ 0 ∧ −x ≤ 0) ∨ (x ≤ 1 ∧ −x ≤ 1)`.  The first
disjunct denotes the point `{0}` and the second the interval `[−1, 1]`, so `Sol(F)` is
`[−1, 1]`.  Every hypothesis of `Ttc.ttc_volume_estimate` other than `hint` holds, and
`Vol(F) > 0`; `hint` fails at the first cube. -/

/-- The witness atoms: `x ≤ 0`, `−x ≤ 0`, `x ≤ 1`, `−x ≤ 1`. -/
def degAtoms : Fin 4 → LinAtom 1
  | 0 => ⟨fun _ => 1, 0⟩
  | 1 => ⟨fun _ => -1, 0⟩
  | 2 => ⟨fun _ => 1, 1⟩
  | 3 => ⟨fun _ => -1, 1⟩

/-- The witness formula `(x ≤ 0 ∧ −x ≤ 0) ∨ (x ≤ 1 ∧ −x ≤ 1)`. -/
def degForm : BForm (Fin 4) :=
  ((BForm.atom 0).and (BForm.atom 1)).or ((BForm.atom 2).and (BForm.atom 3))

/-- The degenerate cube `x ≤ 0 ∧ −x ≤ 0`; its region is the single point `0`. -/
def thinCube : Cube (Fin 4) := [⟨0, true⟩, ⟨1, true⟩]

/-- The full-dimensional cube `x ≤ 1 ∧ −x ≤ 1`; its region is `[−1, 1]`. -/
def fatCube : Cube (Fin 4) := [⟨2, true⟩, ⟨3, true⟩]

/-- `Ttc.toDNF` on the witness formula, computed. -/
theorem toDNF_degForm : toDNF degForm = [thinCube, fatCube] := rfl

/-- The cubes of the witness formula's deduplicated DNF are exactly the two above. -/
theorem mem_toDNFd_degForm {c : Cube (Fin 4)} :
    c ∈ toDNFd degForm ↔ c = thinCube ∨ c = fatCube := by
  rw [mem_toDNFd, toDNF_degForm]
  simp

theorem thinCube_mem : thinCube ∈ toDNFd degForm := mem_toDNFd_degForm.2 (Or.inl rfl)

theorem fatCube_mem : fatCube ∈ toDNFd degForm := mem_toDNFd_degForm.2 (Or.inr rfl)

/-- Membership in the region of a two-literal positive cube, unfolded.  In dimension `1`
the inner product `∑ i, aᵢ xᵢ` is the single product `a₀ · x₀`. -/
theorem mem_region_pair {x : Space 1} {a b : Fin 4} :
    x ∈ region (atomSet degAtoms) [⟨a, true⟩, ⟨b, true⟩]
      ↔ (degAtoms a).coeff 0 * x 0 ≤ (degAtoms a).bound
        ∧ (degAtoms b).coeff 0 * x 0 ≤ (degAtoms b).bound := by
  simp [mem_region_iff, Lit.holds, induced, atomSet, LinAtom.halfspace]

/-- The thin cube denotes `{x | x₀ = 0}`. -/
theorem mem_region_thinCube {x : Space 1} :
    x ∈ region (atomSet degAtoms) thinCube ↔ x 0 = 0 := by
  rw [thinCube, mem_region_pair]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [degAtoms] at h1 h2
    linarith
  · intro h
    simp only [degAtoms]
    constructor <;> · rw [h]; norm_num

/-- The fat cube denotes `{x | |x₀| ≤ 1}`. -/
theorem mem_region_fatCube {x : Space 1} :
    x ∈ region (atomSet degAtoms) fatCube ↔ |x 0| ≤ 1 := by
  rw [fatCube, mem_region_pair]
  simp only [degAtoms, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- The thin cube's region is a single point. -/
theorem region_thinCube_eq : region (atomSet degAtoms) thinCube = {(0 : Space 1)} := by
  ext x
  rw [mem_region_thinCube, Set.mem_singleton_iff]
  constructor
  · intro h
    refine norm_eq_zero.1 ?_
    rw [norm_space_one, h, abs_zero]
  · rintro rfl
    simp

/-- **A single point has empty interior in `ℝ¹`.**  Proved by hand from the norm, so
that no instance about punctured neighbourhoods is needed: the point `(r/2)·e₀` lies in
every ball of radius `r` about `0` and is not `0`. -/
theorem interior_singleton_zero : interior ({(0 : Space 1)} : Set (Space 1)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hx0 : x ∈ ({(0 : Space 1)} : Set (Space 1)) := interior_subset hx
  rw [Set.mem_singleton_iff] at hx0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  set y : Space 1 := EuclideanSpace.single (0 : Fin 1) (r / 2) with hy
  have hy0 : y 0 = r / 2 := by simp [hy]
  have hnorm : ‖y‖ = r / 2 := by
    rw [norm_space_one, hy0, abs_of_pos (by linarith)]
  have hmem : y ∈ Metric.ball x r := by
    rw [hx0, mem_ball_zero_iff, hnorm]
    linarith
  have hy1 : y ∈ ({(0 : Space 1)} : Set (Space 1)) := interior_subset (hball hmem)
  rw [Set.mem_singleton_iff] at hy1
  rw [hy1, norm_zero] at hnorm
  linarith

/-- **The thin cube is degenerate**: nonempty region, empty interior. -/
theorem interior_region_thinCube : interior (region (atomSet degAtoms) thinCube) = ∅ := by
  rw [region_thinCube_eq]; exact interior_singleton_zero

/-- The thin cube's region is nonetheless *nonempty* — this is the hard case, not the
easy "empty cube" one. -/
theorem region_thinCube_nonempty : (region (atomSet degAtoms) thinCube).Nonempty := by
  rw [region_thinCube_eq]; exact ⟨0, rfl⟩

/-- The unit ball sits inside the fat cube's region. -/
theorem ball_subset_region_fatCube :
    Metric.ball (0 : Space 1) 1 ⊆ region (atomSet degAtoms) fatCube := by
  intro x hx
  rw [mem_ball_zero_iff, norm_space_one] at hx
  exact mem_region_fatCube.2 hx.le

/-- The fat cube's region sits inside the closed unit ball. -/
theorem region_fatCube_subset_closedBall :
    region (atomSet degAtoms) fatCube ⊆ Metric.closedBall (0 : Space 1) 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff, norm_space_one]
  exact mem_region_fatCube.1 hx

/-- The fat cube is full-dimensional. -/
theorem interior_region_fatCube_nonempty :
    (interior (region (atomSet degAtoms) fatCube)).Nonempty :=
  interior_nonempty_of_ball_subset one_pos ball_subset_region_fatCube

/-! ### The other hypotheses of `Ttc.ttc_volume_estimate`, checked -/

/-- `hφ`: the witness formula is negation-free. -/
theorem degForm_isPositive : degForm.IsPositive := ⟨⟨trivial, trivial⟩, trivial, trivial⟩

/-- `hbdd`: the witness solution set is bounded — it is `[−1, 1]`. -/
theorem degForm_isBounded : Bornology.IsBounded (sol (atomSet degAtoms) degForm) := by
  refine isBounded_sol_of_isBounded_regions (toDNFd_isDNFOf degForm) ?_
  intro c hc
  rcases mem_toDNFd_degForm.1 hc with rfl | rfl
  · rw [region_thinCube_eq]; exact Set.Finite.isBounded (Set.finite_singleton _)
  · exact Metric.isBounded_closedBall.subset region_fatCube_subset_closedBall

/-- `hcoeff`: no atom of the witness formula has a zero normal. -/
theorem degForm_coeff_ne_zero :
    ∀ j : FacetIndex (toDNFd degForm), (degAtoms j.2.val.atom).coeff ≠ 0 := by
  rintro ⟨⟨c, hc⟩, ⟨l, hl⟩⟩ h
  have hz : (degAtoms l.atom).coeff 0 = 0 := by rw [h]; rfl
  rcases mem_toDNFd_degForm.1 hc with rfl | rfl <;>
    · simp only [thinCube, fatCube, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> · simp [degAtoms] at hz

/-- The witness volume is finite. -/
theorem volume_sol_degForm_ne_top : volume (sol (atomSet degAtoms) degForm) ≠ ⊤ :=
  degForm_isBounded.measure_lt_top.ne

/-- The witness volume is nonzero: the fat cube's region contains a ball. -/
theorem volume_sol_degForm_ne_zero : volume (sol (atomSet degAtoms) degForm) ≠ 0 := by
  intro h
  have hsub : Metric.ball (0 : Space 1) 1 ⊆ sol (atomSet degAtoms) degForm :=
    ball_subset_region_fatCube.trans (region_subset_sol (toDNFd_isDNFOf degForm) fatCube_mem)
  exact (Metric.measure_ball_pos volume (0 : Space 1) one_pos).ne'
    (nonpos_iff_eq_zero.1 (h ▸ measure_mono hsub))

/-- **The conclusion of `Ttc.ttc_volume_estimate` is not vacuous here**: `Vol(F) > 0`,
so `relErr ε (volSol …)` is a genuine interval and not the single point `{0}`.  This is
what makes the counterexample sharp — the failure of `hint` is not accompanied by a
degenerate right-hand side. -/
theorem volSol_degForm_pos : 0 < volSol (atomSet degAtoms) degForm :=
  ENNReal.toReal_pos volume_sol_degForm_ne_zero volume_sol_degForm_ne_top

/-! ### `hint` fails, and the repair destroys `Ttc.IsDNFOf` -/

/-- **`hint` fails on the witness input.** -/
theorem degForm_hint_fails :
    ¬ ∀ i : {c : Cube (Fin 4) // c ∈ toDNFd degForm},
        (interior (region (atomSet degAtoms) i.val)).Nonempty := by
  intro h
  exact (h ⟨thinCube, thinCube_mem⟩).ne_empty interior_region_thinCube

/-- **`hint` is not derivable from the other hypotheses of `Ttc.ttc_volume_estimate`.**

The witness formula is negation-free, its solution set is bounded, no atom has a zero
normal, and its volume is positive — every input condition the theorem carries besides
`hint`, and the parameter conditions `hε0 hε1 hδ0 hδ1 hn` are about `ε`, `δ` and `n`
only.  Yet `hint` fails. -/
theorem hint_not_derivable :
    degForm.IsPositive
      ∧ Bornology.IsBounded (sol (atomSet degAtoms) degForm)
      ∧ (∀ j : FacetIndex (toDNFd degForm), (degAtoms j.2.val.atom).coeff ≠ 0)
      ∧ 0 < volSol (atomSet degAtoms) degForm
      ∧ ¬ ∀ i : {c : Cube (Fin 4) // c ∈ toDNFd degForm},
          (interior (region (atomSet degAtoms) i.val)).Nonempty :=
  ⟨degForm_isPositive, degForm_isBounded, degForm_coeff_ne_zero, volSol_degForm_pos,
    degForm_hint_fails⟩

/-- Pruning the witness DNF leaves exactly the fat cube. -/
theorem mem_nondegenCubes_degForm {c : Cube (Fin 4)} :
    c ∈ nondegenCubes (atomSet degAtoms) (toDNFd degForm) ↔ c = fatCube := by
  rw [mem_nondegenCubes]
  constructor
  · rintro ⟨hc, hint⟩
    rcases mem_toDNFd_degForm.1 hc with rfl | rfl
    · exact absurd interior_region_thinCube hint.ne_empty
    · rfl
  · rintro rfl
    exact ⟨fatCube_mem, interior_region_fatCube_nonempty⟩

/-- **The repair is unavailable: pruning destroys `Ttc.IsDNFOf`.**

`Ttc.IsDNFOf` quantifies over Boolean assignments, so it is destroyed by deleting a
cube even though — here — deleting `Ttc.thinCube` changes the solution *set* not at all
(`{0} ⊆ [−1, 1]`), let alone its measure.  The assignment `v a ↔ a ∈ {0, 1}` satisfies
`degForm` and no surviving cube.

This is the precise obstruction: `Ttc.sol_eq_iUnion_region`, `Ttc.latticeCount` and
`lem:lattice` all consume `Ttc.IsDNFOf`. -/
theorem not_isDNFOf_nondegenCubes_degForm :
    ¬ IsDNFOf (nondegenCubes (atomSet degAtoms) (toDNFd degForm)) degForm := by
  intro h
  have hv := (h (fun a => a = 0 ∨ a = 1)).2 (Or.inl ⟨Or.inl rfl, Or.inr rfl⟩)
  obtain ⟨c, hc, hcv⟩ := hv
  rw [mem_nondegenCubes_degForm] at hc
  subst hc
  have := hcv ⟨2, true⟩ (by simp [fatCube])
  simp [Lit.holds] at this

/-- **The measure really is preserved**, on the witness input: an instance of
`Ttc.volSol_eq_toReal_biUnion_nondegenCubes`.  Both statements of this section hold at
once — the pruned union has the right volume, and it is not a DNF of the formula. -/
theorem volSol_degForm_eq_pruned :
    volSol (atomSet degAtoms) degForm
      = (volume (⋃ c ∈ nondegenCubes (atomSet degAtoms) (toDNFd degForm),
          region (atomSet degAtoms) c)).toReal :=
  volSol_eq_toReal_biUnion_nondegenCubes degAtoms (toDNFd_isDNFOf degForm)

/-! ## Axiom profile -/

#print axioms volume_eq_zero_of_interior_eq_empty
#print axioms volume_region_eq_zero_of_interior_empty
#print axioms nondegenCubes
#print axioms mem_nondegenCubes
#print axioms nondegenCubes_subset
#print axioms volume_biUnion_nondegenCubes
#print axioms volume_sol_eq_volume_biUnion_nondegenCubes
#print axioms volSol_eq_toReal_biUnion_nondegenCubes
#print axioms toDNF_degForm
#print axioms mem_toDNFd_degForm
#print axioms mem_region_pair
#print axioms mem_region_thinCube
#print axioms mem_region_fatCube
#print axioms region_thinCube_eq
#print axioms interior_singleton_zero
#print axioms interior_region_thinCube
#print axioms region_thinCube_nonempty
#print axioms ball_subset_region_fatCube
#print axioms region_fatCube_subset_closedBall
#print axioms interior_region_fatCube_nonempty
#print axioms degForm_isPositive
#print axioms degForm_isBounded
#print axioms degForm_coeff_ne_zero
#print axioms volume_sol_degForm_ne_top
#print axioms volume_sol_degForm_ne_zero
#print axioms volSol_degForm_pos
#print axioms degForm_hint_fails
#print axioms hint_not_derivable
#print axioms mem_nondegenCubes_degForm
#print axioms not_isDNFOf_nondegenCubes_degForm
#print axioms volSol_degForm_eq_pruned

end Ttc
