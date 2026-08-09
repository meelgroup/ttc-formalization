/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Lattice.Decomposition
import Ttc.Model.ProblemSetting
import Arlib.Lattice.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# `Exec/Geometry`: the inscribed ball and the lattice enumeration, constructed

`Ttc.ttc_volume` (`Model/Endgoal.lean`) carries **37 residual binders**.  Eleven of
them are geometry and enumeration:

```lean
normal_ne_zero : ∀ j : FacetIndex (toDNF φ), 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2
cen            : {c : Cube A // c ∈ toDNF φ} → Space n
gammaHat       : ℝ
hgammaHat      : 0 < gammaHat
ball_subset    : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val
volume_ne_top  : ∀ i, volume (region M i.val) ≠ ⊤
Lidx           : ℕ
ptE            : Fin Lidx → Space n
ptE_inj        : Function.Injective ptE
ptE_mem        : ∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ)
ptE_onto       : ∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x
```

This file settles all eleven, and says for each whether it is **constructed** or
**irreducible**.  Nothing here is edited into `Model/Endgoal.lean`; the results are
stated so that a substitution pass can use them verbatim.

## Verdicts

| binder | verdict | by |
| --- | --- | --- |
| `cen`, `gammaHat`, `hgammaHat`, `ball_subset` | **constructed, no new hypothesis** | `Ttc.exists_inscribed_ball_of_vol_pos` |
| `volume_ne_top` | **irreducible**; minimal input condition `Bornology.IsBounded (sol M φ)` | `Ttc.volume_region_ne_top_of_isBounded` |
| `Lidx`, `ptE`, `ptE_inj`, `ptE_mem`, `ptE_onto` | **constructed** from the same boundedness | `Ttc.exists_lattice_enum_of_isBounded` |
| `normal_ne_zero` | **irreducible**; minimal input condition `(atoms a).coeff ≠ 0` for each occurring atom | `Ttc.normal_ne_zero_of_coeff_ne_zero`, and `Ttc.normal_ne_zero_not_derivable` for the non-derivability |

So the eleven collapse to **two** genuine input conditions, both about the input
formula and both checkable by inspection:

* `Bornology.IsBounded (sol M φ)` — the solution set is bounded;
* `∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0` — no atom of the
  formula has a zero normal vector.

## Why the inscribed ball needs no new hypothesis

An inscribed ball exists in `region M c` exactly when that region has nonempty
interior (`Ttc.exists_inscribed_ball` and its converse
`Ttc.interior_nonempty_of_ball_subset` — so this is not merely sufficient, it is
the condition).  For a **convex** set, nonempty interior is equivalent to positive
Lebesgue measure (`Ttc.interior_nonempty_of_measure_ne_zero`, from
`Convex.interior_nonempty_iff_affineSpan_eq_top` and
`MeasureTheory.Measure.addHaar_affineSubspace`), and `Ttc.convex_region` gives
convexity for free in the LRA fragment.  Positive measure is in turn already
implied by two binders `Ttc.ttc_volume` *already has*: `vol_pos` (`0 < vol i`) and
`volCoins_good` (`vol i ∈ relErr ε' (volume (region M i)).toReal`) — a zero-measure
region would force `vol i ≤ 0`.

The finiteness of `{c : Cube A // c ∈ D}` — a `Ttc.DNF` is a `List` — is what lets
the per-cube radii be minimised into a single `γ̂ > 0`
(`Ttc.finite_cube_subtype`, `Finite.exists_min`).

## Why boundedness is irreducible

A polytope need not be bounded, and `ENNReal.toReal ⊤ = 0` silently: an unbounded
`Sol(F)` makes `Ttc.volSol` equal `0` and the capstone vacuous, which
`Ttc.VolSolCheck.volSol_tt_eq_zero` already exhibits.  So *some* finiteness
hypothesis is unavoidable.  Boundedness of `Sol(F)` is the natural one, and it is
**equivalent** to the per-cube form (`Ttc.isBounded_sol_iff_regions`), so it costs
one binder and covers both `volume_ne_top` and the enumeration.

Two sharper remarks, both proved below:

* For the *enumeration* alone the minimal condition is weaker still — finiteness
  of `Sol(F) ∩ 𝕃ⁿ` — and it is **equivalent** to the five binders
  (`Ttc.exists_lattice_enum_of_finite` and its converse
  `Ttc.finite_of_lattice_enum`).
* For `volume_ne_top` the minimal condition is literally itself.  Boundedness
  implies it and not conversely *for general sets*; for a full-dimensional
  polyhedron the two coincide (an unbounded polyhedron with nonempty interior
  contains a translate of a ball along a recession ray, hence has infinite
  volume), but that equivalence needs recession-cone theory and is not proved
  here.

## Why the zero-normal condition is irreducible

`Ttc.normal_ne_zero_not_derivable` is an explicit counterexample: three atoms in
dimension `1` — `x ≤ 1`, `−x ≤ 1` and the degenerate `0·x ≤ 1` — whose cube has a
bounded region with nonempty interior, is a positive DNF, and yet has a facet with
a zero normal.  So boundedness and non-degeneracy of the *body* do not imply
non-degeneracy of the *presentation*.  What a zero normal means is recorded in
`Ttc.halfspace_eq_univ_of_coeff_zero` / `Ttc.halfspace_eq_empty_of_coeff_zero`:
such an atom is either a tautology or a contradiction, so the condition is exactly
"the formula contains no trivial atom", which any preprocessor establishes.
`Ttc.sq_sum_pos_iff` turns the binder's opaque `0 < ∑ k, coeff k ^ 2` into the
readable `coeff ≠ 0`.
-/

namespace Ttc

open MeasureTheory Set

variable {A X : Type*} {n : ℕ}

/-! ## 1. Boundedness: the one input condition, and its per-cube form -/

/-- Each cube's region is bounded when `Sol(F)` is: the region is a subset
(`Ttc.region_subset_sol`). -/
theorem isBounded_region_of_isBounded_sol [Bornology X] {M : A → Set X} {φ : BForm A}
    {D : DNF A} (hD : IsDNFOf D φ) (hb : Bornology.IsBounded (sol M φ))
    {c : Cube A} (hc : c ∈ D) : Bornology.IsBounded (region M c) :=
  hb.subset (region_subset_sol hD hc)

/-- Conversely, `Sol(F)` is bounded when every cube's region is: a `Ttc.DNF` is a
`List`, so the union of `Ttc.sol_eq_iUnion_region` is finite. -/
theorem isBounded_sol_of_isBounded_regions [Bornology X] {M : A → Set X} {φ : BForm A}
    {D : DNF A} (hD : IsDNFOf D φ) (hb : ∀ c ∈ D, Bornology.IsBounded (region M c)) :
    Bornology.IsBounded (sol M φ) := by
  rw [← sol_eq_iUnion_region hD]
  exact (Bornology.isBounded_biUnion (List.finite_toSet D)).2 hb

/-- **The two forms of the boundedness hypothesis are equivalent.**  So carrying
`Bornology.IsBounded (sol M φ)` — one condition about the input formula — costs
nothing against the per-cube form the geometry consumes. -/
theorem isBounded_sol_iff_regions [Bornology X] {M : A → Set X} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) :
    Bornology.IsBounded (sol M φ) ↔ ∀ c ∈ D, Bornology.IsBounded (region M c) :=
  ⟨fun h _ hc => isBounded_region_of_isBounded_sol hD h hc, isBounded_sol_of_isBounded_regions hD⟩

/-! ## 2. `volume_ne_top` -/

/-- A bounded subset of `ℝⁿ` has finite Lebesgue measure. -/
theorem volume_ne_top_of_isBounded {S : Set (Space n)} (hS : Bornology.IsBounded S) :
    volume S ≠ ⊤ := hS.measure_lt_top.ne

/-- **`volume_ne_top`, in the exact shape `Ttc.ttc_volume` asks for.**  The single
input condition `Bornology.IsBounded (sol M φ)` discharges it for every cube. -/
theorem volume_region_ne_top_of_isBounded {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hb : Bornology.IsBounded (sol M φ)) :
    ∀ i : {c : Cube A // c ∈ D}, volume (region M i.val) ≠ ⊤ :=
  fun i => volume_ne_top_of_isBounded (isBounded_region_of_isBounded_sol hD hb i.property)

/-! ## 3. The inscribed ball

`cen`, `gammaHat`, `hgammaHat` and `ball_subset` are four binders for one fact:
each region contains a ball, of a radius that does not depend on the cube.  The
`min` over the finitely many cubes is where the finiteness of a `Ttc.DNF` earns
its keep.
-/

/-- The cubes of a `Ttc.DNF` form a finite type — a `Ttc.DNF` is a `List`. -/
theorem finite_cube_subtype (D : DNF A) : Finite {c : Cube A // c ∈ D} :=
  (List.finite_toSet D).to_subtype

/-- **The inscribed ball exists as soon as every region has nonempty interior.**
Choose an interior point and a radius per cube; the radii are finitely many, so
their minimum is positive and works for all cubes at once.

This is the four binders `cen`, `gammaHat`, `hgammaHat`, `ball_subset` of
`Ttc.ttc_volume`, produced together. -/
theorem exists_inscribed_ball {M : A → Set (Space n)} (D : DNF A)
    (hint : ∀ i : {c : Cube A // c ∈ D}, (interior (region M i.val)).Nonempty) :
    ∃ (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ), 0 < gammaHat ∧
      ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val := by
  have _ : Finite {c : Cube A // c ∈ D} := finite_cube_subtype D
  have hchoice : ∀ i : {c : Cube A // c ∈ D},
      ∃ p : Space n × ℝ, 0 < p.2 ∧ Metric.ball p.1 p.2 ⊆ region M i.val := by
    intro i
    obtain ⟨x, hx⟩ := hint i
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
    exact ⟨(x, r), hr, hball.trans interior_subset⟩
  choose p hp hpsub using hchoice
  rcases isEmpty_or_nonempty {c : Cube A // c ∈ D} with _ | _
  · exact ⟨fun i => isEmptyElim i, 1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min fun i => (p i).2
    exact ⟨fun i => (p i).1, (p i₀).2, hp i₀,
      fun i => (Metric.ball_subset_ball (hi₀ i)).trans (hpsub i)⟩

/-- **The converse: an inscribed ball forces nonempty interior.**  So the
hypothesis of `Ttc.exists_inscribed_ball` is not merely sufficient — it is exactly
what the four binders say, and no weaker condition can do. -/
theorem interior_nonempty_of_ball_subset [PseudoMetricSpace X] {M : A → Set X}
    {c : Cube A} {x : X} {g : ℝ} (hg : 0 < g)
    (h : Metric.ball x g ⊆ region M c) : (interior (region M c)).Nonempty :=
  ⟨x, interior_mono h (by rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self hg)⟩

/-! ### Nonempty interior is free: it follows from positive measure and convexity -/

/-- **A convex set of nonzero measure has nonempty interior.**  If the interior
were empty the affine span would be a proper subspace
(`Convex.interior_nonempty_iff_affineSpan_eq_top`), and a proper affine subspace is
Haar-null (`MeasureTheory.Measure.addHaar_affineSubspace`). -/
theorem interior_nonempty_of_measure_ne_zero {S : Set (Space n)} (hc : Convex ℝ S)
    (h : volume S ≠ 0) : (interior S).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  refine h (measure_mono_null (subset_affineSpan ℝ S) ?_)
  refine Measure.addHaar_affineSubspace volume _ fun htop => ?_
  rw [← hc.interior_nonempty_iff_affineSpan_eq_top, hne] at htop
  exact htop.ne_empty rfl

/-- A region of nonzero measure has nonempty interior: in the LRA fragment it is
convex (`Ttc.convex_region`). -/
theorem interior_region_nonempty_of_volume_ne_zero (atoms : A → LinAtom n) (c : Cube A)
    (h : volume (region (fun a => (atoms a).halfspace) c) ≠ 0) :
    (interior (region (fun a => (atoms a).halfspace) c)).Nonempty :=
  interior_nonempty_of_measure_ne_zero (convex_region atoms c) h

/-- **A positive volume estimate certifies nonzero measure.**  If `volume S = 0`
then `relErr e 0 = {0}`, so no positive `v` lies in it.  This is what makes
`Ttc.ttc_volume`'s existing binders `vol_pos` and `volCoins_good` imply that every
region is full-dimensional. -/
theorem volume_ne_zero_of_mem_relErr {S : Set (Space n)} {v e : ℝ} (hv : 0 < v)
    (hmem : v ∈ relErr e (volume S).toReal) : volume S ≠ 0 := by
  intro h0
  have h2 : v ≤ (1 + e) * (volume S).toReal := hmem.2
  rw [h0, ENNReal.toReal_zero, mul_zero] at h2
  linarith

/-- **The inscribed ball, from binders `Ttc.ttc_volume` already has.**

`hpos` is its `vol_pos` and `hgood` its `volCoins_good`.  Together they say each
region has positive volume; convexity turns that into nonempty interior; the
minimum over the finitely many cubes turns that into a single radius.  **No new
hypothesis is introduced** — `cen`, `gammaHat`, `hgammaHat` and `ball_subset` are
constructed outright. -/
theorem exists_inscribed_ball_of_vol_pos (atoms : A → LinAtom n) (D : DNF A)
    {vol : Cube A → ℝ} {e : ℝ} (hpos : ∀ c ∈ D, 0 < vol c)
    (hgood : ∀ c ∈ D,
      vol c ∈ relErr e (volume (region (fun a => (atoms a).halfspace) c)).toReal) :
    ∃ (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ), 0 < gammaHat ∧
      ∀ i, Metric.ball (cen i) gammaHat ⊆ region (fun a => (atoms a).halfspace) i.val :=
  exists_inscribed_ball D fun i =>
    interior_region_nonempty_of_volume_ne_zero atoms i.val
      (volume_ne_zero_of_mem_relErr (hpos i.val i.property) (hgood i.val i.property))

/-! ## 4. The lattice enumeration

`Lidx`, `ptE`, `ptE_inj`, `ptE_mem`, `ptE_onto` say precisely that
`Sol(F) ∩ 𝕃ⁿ` is finite and that `ptE` enumerates it bijectively.  Nothing else.
-/

/-- `Ttc.fineLattice` is `Arlib.Lattice.fineLattice`, and `Ttc.latticeScale` is
`Arlib.Lattice.latticeScale`; both by `rfl`.  Stated locally so that this file does
not depend on `Ttc/Sampler/Bridge.lean`. -/
private theorem inter_fineLattice_eq_arlib (S : Set (Space n)) (ρ : ℤ) :
    S ∩ fineLattice n (latticeScale ρ)
      = S ∩ Arlib.Lattice.fineLattice n (Arlib.Lattice.latticeScale ρ) := rfl

/-- **A bounded set meets the refined lattice in finitely many points.**
`Arlib.Lattice.finite_inter_fineLattice`, in `Ttc`'s vocabulary. -/
theorem finite_inter_fineLattice {S : Set (Space n)} (ρ : ℤ)
    (hS : Bornology.IsBounded S) : (S ∩ fineLattice n (latticeScale ρ)).Finite := by
  rw [inter_fineLattice_eq_arlib]
  exact Arlib.Lattice.finite_inter_fineLattice (Arlib.Lattice.latticeScale_pos ρ) hS

/-- **The enumeration, from finiteness alone.**  A finite set is equivalent to
`Fin` of its `Set.ncard`, and the enumeration size is then literally the paper's
`N = |Sol(F) ∩ 𝕃ⁿ|`, i.e. `Ttc.latticeCount`.

This is the five binders `Lidx`, `ptE`, `ptE_inj`, `ptE_mem`, `ptE_onto` of
`Ttc.ttc_volume`, produced together and with `Lidx` pinned. -/
theorem exists_lattice_enum_of_finite {M : A → Set (Space n)} {φ : BForm A} (ρ : ℤ)
    (hfin : (sol M φ ∩ fineLattice n (latticeScale ρ)).Finite) :
    ∃ ptE : Fin (latticeCount M φ ρ) → Space n, Function.Injective ptE ∧
      (∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ)) ∧
      (∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x) := by
  have _ : Finite (sol M φ ∩ fineLattice n (latticeScale ρ) : Set (Space n)) := hfin.to_subtype
  have hcard : Nat.card (sol M φ ∩ fineLattice n (latticeScale ρ) : Set (Space n))
      = latticeCount M φ ρ := Nat.card_coe_set_eq _
  obtain e := Finite.equivFinOfCardEq hcard
  refine ⟨fun s => (e.symm s : Space n), fun a b hab => ?_, fun s => (e.symm s).property,
    fun x hx => ⟨e ⟨x, hx⟩, ?_⟩⟩
  · exact e.symm.injective (Subtype.ext hab)
  · simp

/-- **The converse.**  An enumeration in the sense of the five binders forces
`Sol(F) ∩ 𝕃ⁿ` to be finite: it is the range of a function out of `Fin Lidx`.  So
finiteness of that intersection is *exactly* what the five binders assert, and no
weaker input condition can replace them. -/
theorem finite_of_lattice_enum {M : A → Set (Space n)} {φ : BForm A} {ρ : ℤ} {Lidx : ℕ}
    (ptE : Fin Lidx → Space n)
    (_hmem : ∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ))
    (honto : ∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x) :
    (sol M φ ∩ fineLattice n (latticeScale ρ)).Finite := by
  refine (Set.finite_range ptE).subset fun x hx => ?_
  obtain ⟨s, hs⟩ := honto x hx
  exact ⟨s, hs⟩

/-- **The enumeration, from the boundedness of `Sol(F)`.**  This is the form the
substitution into `Ttc.ttc_volume` uses: the *same* single input condition that
discharges `volume_ne_top` also constructs all five enumeration binders. -/
theorem exists_lattice_enum_of_isBounded {M : A → Set (Space n)} {φ : BForm A} (ρ : ℤ)
    (hb : Bornology.IsBounded (sol M φ)) :
    ∃ ptE : Fin (latticeCount M φ ρ) → Space n, Function.Injective ptE ∧
      (∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ)) ∧
      (∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x) :=
  exists_lattice_enum_of_finite ρ (finite_inter_fineLattice ρ hb)

/-! ## 5. The facet normals

`normal_ne_zero` says every facet's normal vector is nonzero.  It is **not**
derivable: a zero normal makes the atom a tautology or a contradiction, and a
tautologous atom is perfectly compatible with a bounded, full-dimensional region.
-/

/-- **`0 < ∑ k, coeff k ^ 2` is exactly `coeff ≠ 0`.**  The binder's opaque form,
made readable. -/
theorem sq_sum_pos_iff (a : LinAtom n) : 0 < ∑ k, a.coeff k ^ 2 ↔ a.coeff ≠ 0 := by
  constructor
  · intro h hc
    rw [hc] at h
    simp at h
  · intro hc
    rcases (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg (a.coeff k)).lt_or_eq
      with h | h
    · exact h
    · refine absurd ?_ hc
      funext k
      have hk := (Finset.sum_eq_zero_iff_of_nonneg
        fun k (_ : k ∈ Finset.univ) => sq_nonneg (a.coeff k)).1 h.symm k (Finset.mem_univ k)
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hk

/-- **`normal_ne_zero` in the exact shape `Ttc.ttc_volume` asks for**, from the
readable input condition "no atom occurring in the formula has a zero normal". -/
theorem normal_ne_zero_of_coeff_ne_zero {atoms : A → LinAtom n} {D : DNF A}
    (h : ∀ j : FacetIndex D, (atoms j.2.val.atom).coeff ≠ 0) :
    ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2 :=
  fun j => (sq_sum_pos_iff _).2 (h j)

/-- The converse, so the reformulation loses nothing. -/
theorem coeff_ne_zero_of_normal_ne_zero {atoms : A → LinAtom n} {D : DNF A}
    (h : ∀ j : FacetIndex D, 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2) :
    ∀ j : FacetIndex D, (atoms j.2.val.atom).coeff ≠ 0 :=
  fun j => (sq_sum_pos_iff _).1 (h j)

/-- A zero-normal atom with a nonnegative bound is a **tautology**. -/
theorem halfspace_eq_univ_of_coeff_zero {a : LinAtom n} (h : a.coeff = 0) (hb : 0 ≤ a.bound) :
    a.halfspace = univ := by
  ext x
  simp [LinAtom.halfspace, h, hb]

/-- A zero-normal atom with a negative bound is a **contradiction**. -/
theorem halfspace_eq_empty_of_coeff_zero {a : LinAtom n} (h : a.coeff = 0) (hb : a.bound < 0) :
    a.halfspace = ∅ := by
  ext x
  simp [LinAtom.halfspace, h, not_le, hb]

/-! ### The counterexample: `normal_ne_zero` is not derivable

Three atoms in dimension `1`: `x ≤ 1`, `−x ≤ 1`, and the degenerate `0·x ≤ 1`.
The cube of all three denotes `[−1, 1]` — bounded, with nonempty interior — and the
DNF is positive; yet its third facet has a zero normal.
-/

/-- The witness atoms: `x ≤ 1`, `−x ≤ 1`, `0·x ≤ 1`. -/
def degenAtoms : Fin 3 → LinAtom 1
  | 0 => ⟨fun _ => 1, 1⟩
  | 1 => ⟨fun _ => -1, 1⟩
  | 2 => ⟨fun _ => 0, 1⟩

/-- The witness cube: the conjunction of the three witness atoms. -/
def degenCube : Cube (Fin 3) := [⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩]

/-- The witness DNF. -/
def degenDNF : DNF (Fin 3) := [degenCube]

/-- The witness formula. -/
def degenForm : BForm (Fin 3) := ((BForm.atom 0).and (BForm.atom 1)).and (BForm.atom 2)

/-- The Euclidean norm in dimension `1` is the absolute value of the coordinate. -/
theorem norm_space_one (x : Space 1) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

/-- The witness region, computed: `−1 ≤ x 0 ≤ 1`. -/
theorem mem_degen_region_iff {x : Space 1} :
    x ∈ region (fun a => (degenAtoms a).halfspace) degenCube ↔ x 0 ≤ 1 ∧ -1 ≤ x 0 := by
  simp only [mem_region_iff, degenCube, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h ⟨0, true⟩ (by tauto)
      simpa [Lit.holds, induced, LinAtom.halfspace, degenAtoms, Fin.sum_univ_one] using this
    · have := h ⟨1, true⟩ (by tauto)
      have h' : -x 0 ≤ 1 := by
        simpa [Lit.holds, induced, LinAtom.halfspace, degenAtoms, Fin.sum_univ_one] using this
      linarith
  · rintro ⟨h1, h2⟩ l hl
    rcases hl with rfl | rfl | rfl
    · simpa [Lit.holds, induced, LinAtom.halfspace, degenAtoms, Fin.sum_univ_one] using h1
    · have : -x 0 ≤ 1 := by linarith
      simpa [Lit.holds, induced, LinAtom.halfspace, degenAtoms, Fin.sum_univ_one] using this
    · simp [Lit.holds, induced, LinAtom.halfspace, degenAtoms]

/-- The witness DNF really is a DNF of the witness formula. -/
theorem degen_isDNFOf : IsDNFOf degenDNF degenForm := by
  intro v
  simp only [degenDNF, degenForm, degenCube, DNF.holds, Cube.holds,
    BForm.holds, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨c, rfl, hc⟩
    exact ⟨⟨hc ⟨0, true⟩ (by tauto), hc ⟨1, true⟩ (by tauto)⟩, hc ⟨2, true⟩ (by tauto)⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩
    refine ⟨_, rfl, ?_⟩
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2

/-- The witness DNF is positive. -/
theorem degen_isPositive : DNF.IsPositive degenDNF := by
  intro c hc l hl
  simp only [degenDNF, List.mem_singleton] at hc
  subst hc
  simp only [degenCube, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl <;> rfl

/-- **`normal_ne_zero` is not derivable.**  Everything else cluster 1 asks for
holds — the DNF is positive, its region is bounded and has nonempty interior — and
yet a facet normal vanishes.  So the binder is a genuine condition on the input
atoms, not a consequence of the geometry. -/
theorem normal_ne_zero_not_derivable :
    IsDNFOf degenDNF degenForm ∧ DNF.IsPositive degenDNF ∧
      Bornology.IsBounded (sol (fun a => (degenAtoms a).halfspace) degenForm) ∧
      (∀ i : {c : Cube (Fin 3) // c ∈ degenDNF},
        (interior (region (fun a => (degenAtoms a).halfspace) i.val)).Nonempty) ∧
      ¬ (∀ j : FacetIndex degenDNF, 0 < ∑ k, (degenAtoms j.2.val.atom).coeff k ^ 2) := by
  have hreg : region (fun a => (degenAtoms a).halfspace) degenCube ⊆ Metric.closedBall 0 1 := by
    intro x hx
    rw [mem_degen_region_iff] at hx
    rw [mem_closedBall_zero_iff, norm_space_one, abs_le]
    exact ⟨hx.2, hx.1⟩
  have hball : Metric.ball (0 : Space 1) 1 ⊆ region (fun a => (degenAtoms a).halfspace) degenCube := by
    intro x hx
    rw [mem_ball_zero_iff, norm_space_one, abs_lt] at hx
    rw [mem_degen_region_iff]
    exact ⟨hx.2.le, hx.1.le⟩
  refine ⟨degen_isDNFOf, degen_isPositive, ?_, ?_, ?_⟩
  · refine isBounded_sol_of_isBounded_regions degen_isDNFOf ?_
    intro c hc
    simp only [degenDNF, List.mem_singleton] at hc
    subst hc
    exact (Metric.isBounded_closedBall).subset hreg
  · rintro ⟨c, hc⟩
    have : c = degenCube := by simpa [degenDNF] using hc
    subst this
    exact interior_nonempty_of_ball_subset one_pos hball
  · intro h
    have hj := h ⟨⟨degenCube, by simp [degenDNF]⟩, ⟨⟨2, true⟩, by simp [degenCube]⟩⟩
    simp [degenAtoms] at hj

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms isBounded_region_of_isBounded_sol
#print axioms isBounded_sol_of_isBounded_regions
#print axioms isBounded_sol_iff_regions
#print axioms volume_ne_top_of_isBounded
#print axioms volume_region_ne_top_of_isBounded
#print axioms finite_cube_subtype
#print axioms exists_inscribed_ball
#print axioms interior_nonempty_of_ball_subset
#print axioms interior_nonempty_of_measure_ne_zero
#print axioms interior_region_nonempty_of_volume_ne_zero
#print axioms volume_ne_zero_of_mem_relErr
#print axioms exists_inscribed_ball_of_vol_pos
#print axioms finite_inter_fineLattice
#print axioms exists_lattice_enum_of_finite
#print axioms finite_of_lattice_enum
#print axioms exists_lattice_enum_of_isBounded
#print axioms sq_sum_pos_iff
#print axioms normal_ne_zero_of_coeff_ne_zero
#print axioms coeff_ne_zero_of_normal_ne_zero
#print axioms halfspace_eq_univ_of_coeff_zero
#print axioms halfspace_eq_empty_of_coeff_zero
#print axioms norm_space_one
#print axioms mem_degen_region_iff
#print axioms degen_isDNFOf
#print axioms degen_isPositive
#print axioms normal_ne_zero_not_derivable

end Ttc
