/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Inputs

/-!
# `Findings/OpenHalfspace`: what `hφ : φ.IsPositive` is actually buying

**Verdict: removing `hφ` from `Ttc.ttc_volume` is a real but bounded
refactor of the DNF→facet-system layer, bought at the price of two extra input
hypotheses — not a bookkeeping change, and not research-scale.**  No new
mathematics is needed: a negated atom never has to reach the counting side at all,
because `¬(⟪a, x⟫ ≤ b)` can be traded for the *closed* atom `⟪−a, x⟫ ≤ −b`
(`Ttc.LinAtom.flip`), and that trade is exact for the volume
(`Ttc.volume_compl_halfspace_eq`, `Ttc.volume_sol_eq_iUnion_posify`).  What it is
*not* exact for is the lattice count (`Ttc.exists_latticeCount_ne_of_open`) and
boundedness (`Ttc.exists_isBounded_region_not_isBounded_posify`), and those two
facts are the whole content of finding 5.

## The three facts this file lands

1. **The volume cannot see the difference.**  `Ttc.volume_halfspace_open_eq`: an
   open half-space and its closure have the same Lebesgue measure, because they
   differ by a hyperplane and a nondegenerate hyperplane is a translate of a
   proper subspace, hence Haar-null (`Ttc.volume_hyperplane_eq_zero`).  Lifted to
   whole formulas — *negations allowed* — by `Ttc.volume_sol_openAtomSet_eq`:
   for a countable atom index type with no degenerate atom, `Vol(Sol(F))` is the
   same whether every atom is read `≤` or `<`.  The hypothesis `a.coeff ≠ 0` is
   necessary: at `a.coeff = 0`, `a.bound = 0` the open set is `∅` and the closed
   one is `Set.univ`.

2. **The count can.**  `Ttc.exists_latticeCount_ne_of_open` exhibits
   `x ≤ 0 ∧ −x ≤ 0` in `n = 1` with no degenerate atom: closed it is `{0}`, open it
   is `∅`.  Same volume (`0` either way), but `latticeCount` is `1` against `0`, at
   **every** precision `ρ` — the origin is a point of every `𝕃¹ = 10^(−ρ)·ℤ`.  A
   hyperplane is Lebesgue-null and is not lattice-null, and `lem:lattice` is
   exactly the bridge between those two quantities.  This is the honest heart of
   the finding.

3. **The closed relaxation is volume-exact but not boundedness-preserving.**
   `Ttc.signAtoms`/`Ttc.posify` turn an arbitrary cube into a *positive* cube over
   `A × Bool` (`Ttc.posify_isPositive`), and
   `Ttc.volume_sol_eq_iUnion_posify` says the relaxed union has exactly the volume
   of `Sol(F)`, for any formula and any DNF of it.  But
   `Ttc.exists_isBounded_region_not_isBounded_posify` shows `hbdd` does **not**
   travel: `x₀ ≤ 0 ∧ ¬(x₀ ≤ 0)` in `ℝ²` has empty (hence bounded) region while its
   positivisation is the line `x₀ = 0`.

## Where the development actually uses closedness

Read the third column as: *is closedness needed for the measure-theoretic
statement, or only because the facet system is written with `≤`?*

| Site | What positivity/closedness does there | Verdict |
| --- | --- | --- |
| `Ttc/Model/Prelude.lean:42` | `LinAtom.halfspace` is `{x \| ⟪a,x⟫ ≤ b}` | definition |
| `Ttc/Model/Prelude.lean:72` | `BForm.IsPositive`, the hypothesis itself | definition |
| `Ttc/Model/Prelude.lean:172,175` | `Cube.IsPositive`, `DNF.IsPositive` | definition |
| `Ttc/Nonconv/Geometry.lean:69` | `FacetSystem.piece` is `f j x ≤ b j + t·w j` | facet-system shape only |
| `Ttc/Nonconv/FacetOfDNF.lean:67` | `region_eq_piece` — **the** conversion; needs every literal positive so `Lit.holds` is `x ∈ halfspace` and not its complement | *only* because `piece` is `≤`; disappears under `Ttc.posify` |
| `Ttc/Nonconv/FacetOfDNF.lean:88` | `body_eq_sol` (`Q = Sol(F)`), consumes the above | ditto |
| `Ttc/Lattice/Assembled.lean:93` (used at `:119`, `:140`) | `lattice_of_dnf`'s `hpos`, only via the two above | ditto |
| `Ttc/Exec/CanonPolytope.lean:255` | `canon_body_eq_smul_region`: region = `Arlib.Polytope.body` (again `≤`) — the sampler's polytope | ditto |
| `Ttc/Exec/CanonPolytope.lean:266,273` | `canon_body_one_eq_region`, `canon_smul_region_subset_body` | ditto |
| `Ttc/Exec/RegimeInputs.lean:195,224,231` | `e2eSampD_almostUniform`, via `canon_*` | ditto |
| `Ttc/Exec/RegimeCube.lean:92,112,144,165,189` | per-cube `lem:lattice`, via `lattice_of_dnf` at singleton DNFs | ditto |
| `Ttc/Exec/CubeBounds.lean:58,75,83,131` | **a different use entirely**: `BForm` has no `false` constructor and `IsPositive (.neg _)` is `False`, so `toDNF φ ≠ []`, which is `hm : 1 ≤ m` | not closedness — see "the residual binder" below |
| `Ttc/Exec/Inputs.lean:96–101` | `inputParams` consumes `hφ` **only** through `toDNFd_ne_nil` | not closedness |
| `Ttc/Model/Theorem.lean:69` | the binder under discussion | — |
| `Ttc/Nonconv/Recentred.lean:195,205` | `isClosed_piece` ⇒ `measurableSet_piece` | measure-theoretic, but *open* half-spaces are measurable too — survives |
| `Arlib/Convexity/Polytope.lean:69,76` | `Polytope.body`/`inflate` are `≤` | definition |
| `Arlib/Convexity/Polytope.lean:186–189` | `inner_center_le_of_ball_subset`: `rw [← closure_ball]; exact (isClosed_body …).closure_subset_iff.2 hball` upgrades the open inscribed ball to a closed one | **genuinely needs closedness**; sole geometric input to `inflate_subset_homothety` (`:232`), hence to every volume bound downstream |
| `Arlib/Lattice/KV97/Escape.lean:68` | `simp only [… not_le] at hz` turns `p ∉ inflate` into a *strict* facet crossing | **genuinely needs `≤`**; with open pieces the degenerate facet `A i = 0` gives the event `0 ≤ 0`, probability `1`, and `facet_escape_prob_le` (`:112–119`) becomes false |
| `Arlib/Lattice/KV97/InflateGeom.lean:119–120` | `closedBall_subset_inflate`, a tight non-strict `linarith` chain | genuinely needs `≤` (only `ball_subset_inflate` would survive) |
| `Arlib/Lattice/KV97/Theorem2.lean:189–190` | `measurableSet_inflated`, from `isClosed_inflated` | measurability only — survives |
| `Arlib/Lattice/KV97/Lemma1.lean:181,463–478` | the lattice count is abstract `[Fintype ι]` + hypotheses | **not** closedness-dependent |

The shape of the table is the point.  Every `Ttc`-side site is of the form "the
facet system is written with `≤`", and is discharged by positivising the cube
rather than by touching the geometry.  The three `Arlib`-side sites that really
need `≤` are never reached by an open half-space under that route, because the
relaxation hands KV97 a closed polytope.

## What a removal would consist of, and the two prices

Recipe, in the order the files would change:

1. `Ttc.signAtoms` and `Ttc.posify` (this file) applied to `Ttc.toDNFd φ` for an
   *arbitrary* `φ`.  `Ttc.posify_isPositive` is unconditional, so
   `Ttc.region_eq_piece`, `Ttc.canon_body_eq_smul_region` and `Ttc.lattice_of_dnf`
   apply **verbatim** — no lemma in `Nonconv/`, `Lattice/` or `Arlib/` is touched.
2. A `disj : DNF A → BForm A` with `IsDNFOf (D.map posify) (disj (D.map posify))`,
   so that the capstone still speaks about a `Ttc.sol`.
3. `Ttc.volume_sol_eq_iUnion_posify` to rewrite the conclusion's
   `volSol` back to the original formula's.  `Ttc.relErr` depends on the volume
   only through its value, so the accuracy statement transfers unchanged.

**Price 1 — `hm` stops being free.**  Step 2 has no total solution: `Ttc.BForm` has
**no `false` constructor**, so the empty DNF has no formula, and `disj` is defined
only on nonempty lists.  Positivity is what currently makes `toDNFd φ ≠ []`
automatic (`Ttc/Exec/CubeBounds.lean:58`).  Without it the theorem grows a binder
`toDNFd φ ≠ []` — Boolean satisfiability of the input formula.

**Price 2 — `hbdd` stops transferring.**  `Ttc.exists_isBounded_region_not_isBounded_posify`.
The relaxation's boundedness has to be assumed of the relaxation, which is
strictly stronger than assuming it of `Sol(F)`.

**And the statement changes meaning in one place.**  `Ttc.latticeCount` occurs in
`Ttc.ttc_volume` as the index type of the sample coins.  After the
refactor the run enumerates the lattice points of the *closed relaxation*, which
is provably a different set (fact 2).  The accuracy conclusion, which is about
`Ttc.volSol`, is unaffected (fact 1) — but the algorithm is counting something
else, and that is a repricing, not bookkeeping.

## What is *not* claimed here

Nothing in this file removes `hφ`, and nothing in it is imported by the capstone.
The `disj` of step 2 is not built; the counting-side error term one would need if
one insisted on counting `Sol(F)` itself rather than its relaxation — a bound on
lattice points lying on facet hyperplanes — is not attempted.
-/

namespace Ttc

open MeasureTheory Set

variable {A : Type*} {n : ℕ}

/-! ## The three sets an atom cuts out -/

/-- The **open** half-space `⟪a, x⟫ < b`: what a *negated* atom's complement is,
up to the boundary. -/
def LinAtom.openHalfspace (a : LinAtom n) : Set (Space n) :=
  {x | ∑ i, a.coeff i * x i < a.bound}

/-- The boundary hyperplane `⟪a, x⟫ = b`. -/
def LinAtom.hyperplane (a : LinAtom n) : Set (Space n) :=
  {x | ∑ i, a.coeff i * x i = a.bound}

@[simp] theorem LinAtom.mem_openHalfspace {a : LinAtom n} {x : Space n} :
    x ∈ a.openHalfspace ↔ ∑ i, a.coeff i * x i < a.bound := Iff.rfl

@[simp] theorem LinAtom.mem_hyperplane {a : LinAtom n} {x : Space n} :
    x ∈ a.hyperplane ↔ ∑ i, a.coeff i * x i = a.bound := Iff.rfl

@[simp] theorem LinAtom.mem_halfspace {a : LinAtom n} {x : Space n} :
    x ∈ a.halfspace ↔ ∑ i, a.coeff i * x i ≤ a.bound := Iff.rfl

/-! ## A nondegenerate atom's hyperplane is null -/

/-- Evaluating an atom's linear form on a coordinate vector reads off a
coefficient. -/
theorem LinAtom.form_single (a : LinAtom n) (i : Fin n) :
    a.form (EuclideanSpace.single i (1 : ℝ)) = a.coeff i := by
  simp [LinAtom.form_apply, mul_ite]

/-- A nondegenerate atom has a nonzero linear form. -/
theorem LinAtom.form_ne_zero (a : LinAtom n) (ha : a.coeff ≠ 0) : a.form ≠ 0 := by
  intro h
  refine ha (funext fun i => ?_)
  have h1 : a.form (EuclideanSpace.single i (1 : ℝ)) = 0 := by rw [h]; rfl
  rw [LinAtom.form_single] at h1
  simpa using h1

/-- **A nondegenerate atom's boundary hyperplane is Lebesgue-null.**

`{x | ⟪a, x⟫ = b}` is a translate of `ker a.form`, a proper subspace of `ℝⁿ`
whenever `a ≠ 0`, and a proper subspace of a finite-dimensional space carries no
Haar mass (`MeasureTheory.Measure.addHaar_submodule`). -/
theorem volume_hyperplane_eq_zero (a : LinAtom n) (ha : a.coeff ≠ 0) :
    volume a.hyperplane = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a.coeff i ≠ 0 := Function.ne_iff.1 ha
  have hf : a.form ≠ 0 := a.form_ne_zero ha
  set y : Space n := EuclideanSpace.single i (1 : ℝ) with hy
  have hfy : a.form y = a.coeff i := a.form_single i
  set x₀ : Space n := (a.bound / a.coeff i) • y with hx₀
  have hfx₀ : a.form x₀ = a.bound := by
    rw [hx₀, map_smul, hfy, smul_eq_mul, div_mul_cancel₀ _ hi]
  have hpre : (fun z => x₀ + z) ⁻¹' a.hyperplane = (LinearMap.ker a.form : Set (Space n)) := by
    ext z
    simp only [Set.mem_preimage, LinAtom.mem_hyperplane, SetLike.mem_coe, LinearMap.mem_ker,
      ← LinAtom.form_apply, map_add, hfx₀]
    constructor
    · intro h; linarith
    · intro h; rw [h, add_zero]
  have hshift := measure_preimage_add (volume : Measure (Space n)) x₀ a.hyperplane
  rw [hpre] at hshift
  rw [← hshift]
  exact Measure.addHaar_submodule volume _ (by simpa [LinearMap.ker_eq_top] using hf)

/-! ## Step 1: the volume does not see the difference -/

/-- **An open half-space and its closure have the same volume.**

They differ by the boundary hyperplane, which is null (`Ttc.volume_hyperplane_eq_zero`).
The nondegeneracy hypothesis `a.coeff ≠ 0` is *necessary*, not decorative: at
`a.coeff = 0`, `a.bound = 0` the open set is `∅` and the closed one is
`Set.univ`. -/
theorem volume_halfspace_open_eq (a : LinAtom n) (ha : a.coeff ≠ 0) :
    volume a.openHalfspace = volume a.halfspace := by
  refine le_antisymm (measure_mono fun x hx =>
    LinAtom.mem_halfspace.2 (le_of_lt (LinAtom.mem_openHalfspace.1 hx))) ?_
  have hsub : a.halfspace ⊆ a.openHalfspace ∪ a.hyperplane := by
    intro x hx
    rcases lt_or_eq_of_le (LinAtom.mem_halfspace.1 hx) with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc volume a.halfspace ≤ volume (a.openHalfspace ∪ a.hyperplane) := measure_mono hsub
    _ ≤ volume a.openHalfspace + volume a.hyperplane := measure_union_le _ _
    _ = volume a.openHalfspace := by rw [volume_hyperplane_eq_zero a ha, add_zero]

/-! ## The closed atom a negated literal *would* be replaced by -/

/-- **The flipped atom.**  `¬(⟪a, x⟫ ≤ b)` is `⟪a, x⟫ > b`; the smallest closed
half-space containing it is `⟪a, x⟫ ≥ b`, which is the closed atom
`⟪−a, x⟫ ≤ −b`.  This is the substitution any removal of `hφ` has to make. -/
def LinAtom.flip (a : LinAtom n) : LinAtom n := ⟨-a.coeff, -a.bound⟩

@[simp] theorem LinAtom.flip_sum (a : LinAtom n) (x : Space n) :
    ∑ i, a.flip.coeff i * x i = -∑ i, a.coeff i * x i := by
  simp [LinAtom.flip, neg_mul, Finset.sum_neg_distrib]

@[simp] theorem LinAtom.flip_bound (a : LinAtom n) : a.flip.bound = -a.bound := rfl

theorem LinAtom.flip_coeff_ne_zero {a : LinAtom n} (ha : a.coeff ≠ 0) : a.flip.coeff ≠ 0 := by
  simpa [LinAtom.flip] using ha

theorem LinAtom.flip_hyperplane (a : LinAtom n) : a.flip.hyperplane = a.hyperplane := by
  ext x; simp [LinAtom.hyperplane]

/-- **A negated atom's set and its closed replacement have the same volume.**

`(a.halfspace)ᶜ` is the open half-space `⟪a, x⟫ > b`; `a.flip.halfspace` is the
closed one `⟪a, x⟫ ≥ b`.  They differ by the null hyperplane. -/
theorem volume_compl_halfspace_eq (a : LinAtom n) (ha : a.coeff ≠ 0) :
    volume (a.halfspaceᶜ) = volume a.flip.halfspace := by
  refine le_antisymm (measure_mono ?_) ?_
  · intro x hx
    have h : ¬ (∑ i, a.coeff i * x i ≤ a.bound) := hx
    push Not at h
    simpa using h.le
  · have hsub : a.flip.halfspace ⊆ a.halfspaceᶜ ∪ a.hyperplane := by
      intro x hx
      have h : -∑ i, a.coeff i * x i ≤ -a.bound := by simpa using hx
      rcases lt_or_eq_of_le (neg_le_neg_iff.1 h) with hlt | heq
      · exact Or.inl (by simpa using not_le.2 hlt)
      · exact Or.inr (by simpa using heq.symm)
    calc volume a.flip.halfspace ≤ volume (a.halfspaceᶜ ∪ a.hyperplane) := measure_mono hsub
      _ ≤ volume (a.halfspaceᶜ) + volume a.hyperplane := measure_union_le _ _
      _ = volume (a.halfspaceᶜ) := by rw [volume_hyperplane_eq_zero a ha, add_zero]

/-! ## Step 2: the whole solution set, negations and all -/

/-- **The open interpretation of an atom family**, the sibling of
`Ttc.atomSet` (`Exec/Inputs`). -/
def openAtomSet (atoms : A → LinAtom n) : A → Set (Space n) :=
  fun a => (atoms a).openHalfspace

/-- Off every boundary hyperplane the two interpretations induce the **same**
Boolean assignment, hence agree on every formula — negations included. -/
theorem induced_openAtomSet_eq (atoms : A → LinAtom n) {x : Space n}
    (hx : ∀ a, x ∉ (atoms a).hyperplane) :
    induced (openAtomSet atoms) x = induced (atomSet atoms) x := by
  funext a
  have h : ∑ i, (atoms a).coeff i * x i ≠ (atoms a).bound := hx a
  show (x ∈ (atoms a).openHalfspace) = (x ∈ (atoms a).halfspace)
  simp only [LinAtom.mem_openHalfspace, LinAtom.mem_halfspace]
  exact propext ⟨le_of_lt, fun hle => lt_of_le_of_ne hle h⟩

/-- The two solution sets agree away from the union of the atoms' hyperplanes.
No positivity is needed: the argument goes through `Ttc.induced`, so it is blind
to the shape of `φ`. -/
theorem sol_diff_hyperplanes (atoms : A → LinAtom n) (φ : BForm A) :
    sol (openAtomSet atoms) φ \ (⋃ a, (atoms a).hyperplane)
      = sol (atomSet atoms) φ \ (⋃ a, (atoms a).hyperplane) := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_iUnion, not_exists]
  constructor
  · rintro ⟨hs, hn⟩
    exact ⟨by rwa [mem_sol_iff, ← induced_openAtomSet_eq atoms hn], hn⟩
  · rintro ⟨hs, hn⟩
    exact ⟨by rwa [mem_sol_iff, induced_openAtomSet_eq atoms hn], hn⟩

/-- **`Vol(F)` does not depend on whether the atoms are read open or closed** —
for *any* formula, negations allowed, as long as the atom index type is countable
and no atom is degenerate. -/
theorem volume_sol_openAtomSet_eq [Countable A] (atoms : A → LinAtom n)
    (ha : ∀ a, (atoms a).coeff ≠ 0) (φ : BForm A) :
    volume (sol (openAtomSet atoms) φ) = volume (sol (atomSet atoms) φ) := by
  have hnull : volume (⋃ a, (atoms a).hyperplane) = 0 :=
    measure_iUnion_null fun a => volume_hyperplane_eq_zero (atoms a) (ha a)
  rw [← measure_sdiff_null (s := sol (openAtomSet atoms) φ) hnull,
    ← measure_sdiff_null (s := sol (atomSet atoms) φ) hnull, sol_diff_hyperplanes]

/-- The `Ttc.volSol` form of `Ttc.volume_sol_openAtomSet_eq`. -/
theorem volSol_openAtomSet_eq [Countable A] (atoms : A → LinAtom n)
    (ha : ∀ a, (atoms a).coeff ≠ 0) (φ : BForm A) :
    volSol (openAtomSet atoms) φ = volSol (atomSet atoms) φ := by
  simp only [volSol, volume_sol_openAtomSet_eq atoms ha φ]

/-! ## What a removal of `hφ` would have to build: the signed relaxation

A negated literal `¬a` can be traded for a **positive** literal over the flipped
atom `Ttc.LinAtom.flip`.  Doing that to a whole DNF gives a positive DNF over the
index type `A × Bool`, to which the entire `lem:nonconv`/`lem:lattice` chain
already applies verbatim — and the theorems below say it costs nothing in volume.
-/

/-- **The signed atom family.**  `(a, true)` is `a` itself; `(a, false)` is the
closed half-space `⟪a, x⟫ ≥ b` that replaces `¬a`. -/
def signAtoms (atoms : A → LinAtom n) : A × Bool → LinAtom n
  | (a, true) => atoms a
  | (a, false) => (atoms a).flip

/-- **Positivising a cube**: each literal `⟨a, p⟩` becomes the *positive* literal
`⟨(a, p), true⟩` over the signed index type. -/
def posify (c : Cube A) : Cube (A × Bool) := c.map fun l => ⟨(l.atom, l.pos), true⟩

/-- Positivised cubes are positive — by construction, with no hypothesis on `c`. -/
theorem posify_isPositive (c : Cube A) : Cube.IsPositive (posify c) := by
  intro l hl
  obtain ⟨l', _, rfl⟩ := List.mem_map.1 hl
  rfl

/-- The signed family has no degenerate atom if the original has none. -/
theorem signAtoms_coeff_ne_zero {atoms : A → LinAtom n} (ha : ∀ a, (atoms a).coeff ≠ 0) :
    ∀ p, (signAtoms atoms p).coeff ≠ 0 := by
  rintro ⟨a, (_ | _)⟩
  · exact LinAtom.flip_coeff_ne_zero (ha a)
  · exact ha a

/-- **The literal-level trade**, off the boundary: a positive literal over the
flipped atom holds exactly where the negated literal did. -/
theorem holds_posify_lit (atoms : A → LinAtom n) {x : Space n}
    (hx : ∀ a, x ∉ (atoms a).hyperplane) (l : Lit A) :
    (Lit.mk (l.atom, l.pos) true).holds (induced (atomSet (signAtoms atoms)) x)
      ↔ l.holds (induced (atomSet atoms) x) := by
  obtain ⟨a, p⟩ := l
  have h : ∑ i, (atoms a).coeff i * x i ≠ (atoms a).bound := hx a
  cases p
  · show x ∈ (atoms a).flip.halfspace ↔ ¬ (x ∈ (atoms a).halfspace)
    simp only [LinAtom.mem_halfspace, LinAtom.flip_sum, LinAtom.flip_bound, not_le]
    constructor
    · intro hle
      exact lt_of_le_of_ne (neg_le_neg_iff.1 hle) (Ne.symm h)
    · intro hlt
      exact neg_le_neg_iff.2 hlt.le
  · exact Iff.rfl

/-- **The cube-level trade**, off the boundary. -/
theorem mem_region_posify_iff (atoms : A → LinAtom n) {x : Space n}
    (hx : ∀ a, x ∉ (atoms a).hyperplane) (c : Cube A) :
    x ∈ region (atomSet (signAtoms atoms)) (posify c) ↔ x ∈ region (atomSet atoms) c := by
  simp only [mem_region_iff, posify, List.mem_map]
  constructor
  · intro h l hl
    exact (holds_posify_lit atoms hx l).1 (h _ ⟨l, hl, rfl⟩)
  · rintro h _ ⟨l, hl, rfl⟩
    exact (holds_posify_lit atoms hx l).2 (h l hl)

/-- **The signed relaxation is volume-exact.**

The union of the positivised cubes' regions, read over the signed atoms, has
exactly the volume of the original union — for an *arbitrary* DNF, negated
literals included. -/
theorem volume_iUnion_region_posify [Countable A] (atoms : A → LinAtom n)
    (ha : ∀ a, (atoms a).coeff ≠ 0) (D : DNF A) :
    volume (⋃ c ∈ D, region (atomSet (signAtoms atoms)) (posify c))
      = volume (⋃ c ∈ D, region (atomSet atoms) c) := by
  have hnull : volume (⋃ a, (atoms a).hyperplane) = 0 :=
    measure_iUnion_null fun a => volume_hyperplane_eq_zero (atoms a) (ha a)
  have hdiff : (⋃ c ∈ D, region (atomSet (signAtoms atoms)) (posify c))
        \ (⋃ a, (atoms a).hyperplane)
      = (⋃ c ∈ D, region (atomSet atoms) c) \ (⋃ a, (atoms a).hyperplane) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_iUnion, not_exists]
    constructor
    · rintro ⟨⟨c, hc, hx⟩, hn⟩
      exact ⟨⟨c, hc, (mem_region_posify_iff atoms hn c).1 hx⟩, hn⟩
    · rintro ⟨⟨c, hc, hx⟩, hn⟩
      exact ⟨⟨c, hc, (mem_region_posify_iff atoms hn c).2 hx⟩, hn⟩
  rw [← measure_sdiff_null (s := ⋃ c ∈ D, region (atomSet (signAtoms atoms)) (posify c)) hnull,
    ← measure_sdiff_null (s := ⋃ c ∈ D, region (atomSet atoms) c) hnull, hdiff]

/-- **`Vol(F)` is computed exactly by the signed relaxation**, for any formula and
any DNF of it — no positivity hypothesis anywhere. -/
theorem volume_sol_eq_iUnion_posify [Countable A] (atoms : A → LinAtom n)
    (ha : ∀ a, (atoms a).coeff ≠ 0) {D : DNF A} {φ : BForm A} (hDNF : IsDNFOf D φ) :
    volume (⋃ c ∈ D, region (atomSet (signAtoms atoms)) (posify c))
      = volume (sol (atomSet atoms) φ) := by
  rw [volume_iUnion_region_posify atoms ha D, sol_eq_iUnion_region hDNF]

/-! ## Step 3: the count *does* see the difference -/

namespace OpenHalfspace

/-- Two atoms in dimension one: `x ≤ 0` at index `true`, `−x ≤ 0` at index
`false`. -/
def pinAtoms : Bool → LinAtom 1
  | true => ⟨fun _ => 1, 0⟩
  | false => ⟨fun _ => -1, 0⟩

/-- `x ≤ 0 ∧ −x ≤ 0` — closed, this pins `x` to the origin; open, it is
unsatisfiable. -/
def pinForm : BForm Bool := (BForm.atom true).and (BForm.atom false)

theorem pinAtoms_coeff_ne_zero : ∀ b, (pinAtoms b).coeff ≠ 0 := by
  intro b h
  cases b <;>
    · have := congrFun h (0 : Fin 1)
      simp [pinAtoms] at this

theorem sol_pin_closed : sol (atomSet pinAtoms) pinForm = {0} := by
  ext x
  simp only [mem_sol_iff, pinForm, BForm.holds, induced, atomSet, pinAtoms, LinAtom.halfspace,
    Set.mem_setOf_eq, Fin.sum_univ_one, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine PiLp.ext fun i => ?_
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    show x 0 = (0 : Space 1) 0
    simp only [PiLp.zero_apply]
    linarith
  · rintro rfl
    simp

theorem sol_pin_open : sol (openAtomSet pinAtoms) pinForm = ∅ := by
  ext x
  simp only [mem_sol_iff, pinForm, BForm.holds, induced, openAtomSet, pinAtoms,
    LinAtom.openHalfspace, Set.mem_setOf_eq, Fin.sum_univ_one, Set.mem_empty_iff_false, iff_false,
    not_and, not_lt]
  intro h1
  linarith

theorem latticeCount_pin_open (ρ : ℤ) : latticeCount (openAtomSet pinAtoms) pinForm ρ = 0 := by
  simp [latticeCount, sol_pin_open]

theorem latticeCount_pin_closed (ρ : ℤ) : latticeCount (atomSet pinAtoms) pinForm ρ = 1 := by
  have h0 : (0 : Space 1) ∈ fineLattice 1 (latticeScale ρ) := fun i => ⟨0, by simp⟩
  rw [latticeCount, sol_pin_closed,
    Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.2 h0), Set.ncard_singleton]

/-! ### The price of the signed relaxation: `hbdd` does not survive it -/

/-- One atom in dimension two: `x₀ ≤ 0`. -/
def slabAtom : Unit → LinAtom 2 := fun _ => ⟨fun i => if i = 0 then 1 else 0, 0⟩

/-- `x₀ ≤ 0 ∧ ¬(x₀ ≤ 0)` as a cube — unsatisfiable, hence bounded. -/
def slabCube : Cube Unit := [⟨(), true⟩, ⟨(), false⟩]

theorem slab_sum (x : Space 2) : ∑ i, (slabAtom ()).coeff i * x i = x 0 := by
  simp [slabAtom]

theorem region_slabCube_eq_empty : region (atomSet slabAtom) slabCube = ∅ := by
  ext x
  constructor
  · intro h
    exact absurd (h ⟨(), true⟩ (by simp [slabCube])) (h ⟨(), false⟩ (by simp [slabCube]))
  · intro h; exact h.elim

theorem mem_region_posify_slabCube (t : ℝ) :
    (EuclideanSpace.single (1 : Fin 2) t)
      ∈ region (atomSet (signAtoms slabAtom)) (posify slabCube) := by
  intro l hl
  simp only [posify, slabCube, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · show _ ∈ (signAtoms slabAtom ((), true)).halfspace
    simp [signAtoms, LinAtom.halfspace, slabAtom]
  · show _ ∈ (signAtoms slabAtom ((), false)).halfspace
    simp [signAtoms, LinAtom.halfspace, slabAtom]

theorem not_isBounded_region_posify_slabCube :
    ¬ Bornology.IsBounded (region (atomSet (signAtoms slabAtom)) (posify slabCube)) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : Space 2)]
  rintro ⟨r, hr⟩
  have hmem := hr (mem_region_posify_slabCube (|r| + 1))
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  have hn : ‖(EuclideanSpace.single (1 : Fin 2) (|r| + 1) : Space 2)‖ = |r| + 1 := by
    simp [abs_of_nonneg (by positivity : (0:ℝ) ≤ |r| + 1)]
  rw [hn] at hmem
  have := le_abs_self r
  linarith

end OpenHalfspace

/-- **The signed relaxation is volume-exact but not boundedness-preserving.**

`x₀ ≤ 0 ∧ ¬(x₀ ≤ 0)` in `ℝ²` has empty region — bounded — while its positivised
form is the line `x₀ = 0`, which is not.  So a removal of `hφ` cannot reuse
`hbdd : IsBounded (sol (atomSet atoms) φ)`: the relaxation the counting side needs
must be assumed bounded separately, and that is a *strictly stronger* hypothesis
on the input. -/
theorem exists_isBounded_region_not_isBounded_posify :
    ∃ (B : Type) (m : ℕ) (atoms : B → LinAtom m) (c : Cube B),
      Bornology.IsBounded (region (atomSet atoms) c) ∧
      ¬ Bornology.IsBounded (region (atomSet (signAtoms atoms)) (posify c)) :=
  ⟨Unit, 2, OpenHalfspace.slabAtom, OpenHalfspace.slabCube,
    by rw [OpenHalfspace.region_slabCube_eq_empty]; exact Bornology.isBounded_empty,
    OpenHalfspace.not_isBounded_region_posify_slabCube⟩

/-- **The honest heart of finding 5.**  There is a one-dimensional instance, with
no degenerate atom, on which the open and the closed reading of the atoms give the
**same volume** but **different lattice counts** — at every precision `ρ`.

`x ≤ 0 ∧ −x ≤ 0` is `{0}` closed and `∅` open: volume `0` either way, but the
origin is a lattice point of every `𝕃¹ = 10^(−ρ)·ℤ`, so the counts are `1` and
`0`.  A hyperplane is Lebesgue-null and is *not* lattice-null, and `lem:lattice`
relates exactly these two quantities. -/
theorem exists_latticeCount_ne_of_open :
    ∃ (B : Type) (m : ℕ) (atoms : B → LinAtom m) (ψ : BForm B) (ρ : ℤ),
      (∀ b, (atoms b).coeff ≠ 0) ∧
      volSol (openAtomSet atoms) ψ = volSol (atomSet atoms) ψ ∧
      latticeCount (openAtomSet atoms) ψ ρ ≠ latticeCount (atomSet atoms) ψ ρ :=
  ⟨Bool, 1, OpenHalfspace.pinAtoms, OpenHalfspace.pinForm, 0,
    OpenHalfspace.pinAtoms_coeff_ne_zero,
    volSol_openAtomSet_eq _ OpenHalfspace.pinAtoms_coeff_ne_zero _,
    by rw [OpenHalfspace.latticeCount_pin_open, OpenHalfspace.latticeCount_pin_closed]
       exact zero_ne_one⟩

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.volume_hyperplane_eq_zero
#print axioms Ttc.volume_halfspace_open_eq
#print axioms Ttc.volume_compl_halfspace_eq
#print axioms Ttc.volume_sol_openAtomSet_eq
#print axioms Ttc.volSol_openAtomSet_eq
#print axioms Ttc.posify_isPositive
#print axioms Ttc.signAtoms_coeff_ne_zero
#print axioms Ttc.mem_region_posify_iff
#print axioms Ttc.volume_iUnion_region_posify
#print axioms Ttc.volume_sol_eq_iUnion_posify
#print axioms Ttc.exists_isBounded_region_not_isBounded_posify
#print axioms Ttc.exists_latticeCount_ne_of_open
