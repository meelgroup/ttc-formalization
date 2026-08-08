/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.EndToEnd

/-!
# `Exec/CanonicalPolytope`: the linear description is not an assumption

`Ttc.ttc_volume_endToEnd` (`Exec/EndToEnd`) is oracle-free, but it still binds a
**linear description of the input polytopes** as nine separate binders:

```
(Jt : Type) [Fintype Jt]
(Am : {c : Cube A // c ∈ toDNF φ} → Jt → Space n)
(bv : {c : Cube A // c ∈ toDNF φ} → Jt → ℝ)
(hdil : ∀ i, latticeScale (P.precision γ̂) • region M i.val ⊆ body (Am i) (bv i))
(rfac : ℝ) (hr1 : 1 ≤ rfac) (hcard : (Fintype.card Jt : ℝ) ≤ rfac)
(Dm : {c : Cube A // c ∈ toDNF φ} → ℝ)
(hDbody : ∀ i, ∀ x ∈ body (Am i) (bv i), ∀ y ∈ body (Am i) (bv i), dist x y ≤ Dm i)
```

For a **positive** DNF none of these is an assumption: the description is
canonical, and this file *computes* it.

## The observation

`Ttc.region M c = {x | c.holds (induced M x)}` and, with `M a = (atoms a).halfspace`
`= {x | ∑ i, (atoms a).coeff i * x i ≤ (atoms a).bound}`, a **positive** literal `l`
of `c` says exactly `∑ i, (atoms l.atom).coeff i * x i ≤ (atoms l.atom).bound`.  In
`Ttc.Space n = EuclideanSpace ℝ (Fin n)` that sum *is* the real inner product
(`Arlib.KV97.inner_eq_sum_coords`, restated here as `Ttc.mem_halfspace_iff_inner`), so
`region M c` is literally an `Arlib.Polytope.body`.

## The index type, and the padding row

`Arlib.Polytope.body` is indexed by a **single** type `Jt` shared by all cubes, while
each cube has its own literals.  The index chosen here is the facet index the capstone
already carries, `Ttc.FacetIndex (toDNF φ)`, transported to `Fin (Nat.card …)` by
`Ttc.facetEquiv` so that `Jt : Type` (universe `0`) holds for an `A` in *any*
universe.  A facet `j` belonging to a cube other than `i` contributes the **padding
row** `⟪0, x⟫ ≤ 0`, which every point satisfies.  That the padded system still cuts
out the same set is *proved*, not assumed: `Ttc.body_canon_eq` is an **equality**

```
body (canonNormal atoms i) (canonOffset atoms ρ i) = latticeScale ρ • region M i.val
```

so the padding rows cost nothing, and — because the description is *exact* rather
than merely a superset — the diameter bound `hDbody` is the diameter of the dilated
region itself (`Ttc.canonDiam`), which the capstone's own `hbdd` already bounds.

`hcard` comes out against the capstone's existing binder
`hr : 1 ≤ Nat.card (FacetIndex (toDNF φ))` with **no loss**: `rfac` is taken to be
`Nat.card (FacetIndex (toDNF φ))` itself, and `Fintype.card (Fin (Nat.card …))` is
that number on the nose.

## Main results

* `Ttc.region_eq_body_facet` — a positive cube's region *is* a `body`.
* `Ttc.smul_body` — scaling a half-space system scales its offsets.
* `Ttc.body_canon_eq` — the canonical description, an equality.
* `Ttc.hDbody_canonical` — the diameter bound, from `hbdd` alone.
* `Ttc.ttc_volume_endToEnd_canonical` — **the payoff**: `Ttc.ttc_volume_endToEnd`
  with all nine description binders gone.
* `Ttc.Box.ttc_volume_endToEnd_canonical_box_at` and
  `Ttc.Box.exists_two_ttc_volume_endToEnd_canonical_instances` — non-vacuity, at two
  different accuracy pairs.
-/

namespace Ttc

open MeasureTheory Set Pointwise
open scoped InnerProductSpace

variable {A : Type*} {n : ℕ}

/-! ## The half-space of an atom, as a row of a linear system -/

/-- **`Ttc.LinAtom.halfspace` is an `Arlib.Polytope` row.**  `Ttc.sum_mul_eq_inner`
(`Nonconv/BallFacet`, itself `Arlib.KV97.inner_eq_sum_coords`) already identifies
`∑ i, a i · x i` with `⟪a, x⟫_ℝ` in `Ttc.Space n`; this is that identification read
on `Ttc.LinAtom.halfspace`. -/
theorem mem_halfspace_iff_inner (a : LinAtom n) (x : Space n) :
    x ∈ a.halfspace ↔ ⟪coeffPt a.coeff, x⟫_ℝ ≤ a.bound := by
  rw [LinAtom.halfspace, Set.mem_setOf_eq, sum_mul_eq_inner]

/-- A **positive** literal is a single half-space row. -/
theorem lit_holds_iff_inner {atoms : A → LinAtom n} {l : Lit A} (hl : l.pos = true)
    (x : Space n) :
    l.holds (induced (fun a => (atoms a).halfspace) x)
      ↔ ⟪coeffPt (atoms l.atom).coeff, x⟫_ℝ ≤ (atoms l.atom).bound := by
  simp only [Lit.holds, hl, cond_true]
  exact mem_halfspace_iff_inner _ x

/-! ## The canonical index type

`Ttc.FacetIndex D` is finite (a DNF is a *list* of cubes, each a *list* of literals),
so it is equivalent to `Fin (Nat.card (FacetIndex D))` — which lives in `Type 0`, as
`Ttc.ttc_volume_endToEnd`'s `Jt` must, whatever universe `A` lives in.
-/

/-- The facets of a DNF, enumerated.  Finiteness is `Ttc.instFiniteFacetIndex`
(`Exec/Params`), which the capstone already carries.  Only the existence of the
enumeration is used; no property of it is assumed anywhere. -/
noncomputable def facetEquiv (D : DNF A) :
    FacetIndex D ≃ Fin (Nat.card (FacetIndex D)) := Finite.equivFin _

/-! ## The canonical rows

Row `j` of cube `i`'s system is the coefficient vector of `j`'s literal when `j` is a
facet **of `i`**, and the padding row `⟪0, x⟫ ≤ 0` otherwise.
-/

/-- The canonical facet normal: the atom's coefficient vector on `i`'s own facets, and
`0` — the padding row — on every other cube's. -/
noncomputable def facetAm (atoms : A → LinAtom n) {D : DNF A}
    (i : {c : Cube A // c ∈ D}) (j : FacetIndex D) : Space n :=
  haveI := Classical.propDecidable (j.1 = i)
  if j.1 = i then coeffPt (atoms j.2.val.atom).coeff else 0

/-- The canonical facet offset, at dilation `1`.  The padding row's offset is `0`, so
the padding row reads `0 ≤ 0`. -/
noncomputable def facetBv (atoms : A → LinAtom n) {D : DNF A}
    (i : {c : Cube A // c ∈ D}) (j : FacetIndex D) : ℝ :=
  haveI := Classical.propDecidable (j.1 = i)
  if j.1 = i then (atoms j.2.val.atom).bound else 0

theorem facetAm_of_eq (atoms : A → LinAtom n) {D : DNF A}
    {i : {c : Cube A // c ∈ D}} {j : FacetIndex D} (h : j.1 = i) :
    facetAm atoms i j = coeffPt (atoms j.2.val.atom).coeff := by
  rw [facetAm]; exact if_pos h

theorem facetAm_of_ne (atoms : A → LinAtom n) {D : DNF A}
    {i : {c : Cube A // c ∈ D}} {j : FacetIndex D} (h : ¬ j.1 = i) :
    facetAm atoms i j = 0 := by
  rw [facetAm]; exact if_neg h

theorem facetBv_of_eq (atoms : A → LinAtom n) {D : DNF A}
    {i : {c : Cube A // c ∈ D}} {j : FacetIndex D} (h : j.1 = i) :
    facetBv atoms i j = (atoms j.2.val.atom).bound := by
  rw [facetBv]; exact if_pos h

theorem facetBv_of_ne (atoms : A → LinAtom n) {D : DNF A}
    {i : {c : Cube A // c ∈ D}} {j : FacetIndex D} (h : ¬ j.1 = i) :
    facetBv atoms i j = 0 := by
  rw [facetBv]; exact if_neg h

/-- **A positive cube's region *is* a polytope body** — with the padding rows
included, and as an *equality*: nothing is assumed about the description, and the
padding rows are proved harmless rather than waved away. -/
theorem region_eq_body_facet (atoms : A → LinAtom n) {D : DNF A}
    (i : {c : Cube A // c ∈ D}) (hi : Cube.IsPositive i.val) :
    region (fun a => (atoms a).halfspace) i.val
      = Arlib.Polytope.body (facetAm atoms i) (facetBv atoms i) := by
  ext x
  simp only [mem_region_iff, Arlib.Polytope.mem_body]
  constructor
  · intro h j
    by_cases hj : j.1 = i
    · rw [facetAm_of_eq atoms hj, facetBv_of_eq atoms hj]
      have hl : j.2.val ∈ i.val := hj ▸ j.2.property
      exact (lit_holds_iff_inner (hi _ hl) x).1 (h _ hl)
    · rw [facetAm_of_ne atoms hj, facetBv_of_ne atoms hj]
      simp
  · intro h l hl
    have hj := h ⟨i, ⟨l, hl⟩⟩
    rw [facetAm_of_eq atoms (rfl : (⟨i, ⟨l, hl⟩⟩ : FacetIndex D).1 = i),
      facetBv_of_eq atoms (rfl : (⟨i, ⟨l, hl⟩⟩ : FacetIndex D).1 = i)] at hj
    exact (lit_holds_iff_inner (hi _ hl) x).2 hj

/-! ## Dilating a half-space system -/

/-- **Scaling a half-space system scales its offsets.**  This is the equality behind
`Ttc.ttc_volume_endToEnd`'s `hdil`; the theorem only needs `⊆`, but the two sides are
equal. -/
theorem smul_body {ι : Type*} (Am : ι → Space n) (bv : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    s • Arlib.Polytope.body Am bv = Arlib.Polytope.body Am (fun j => s * bv j) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    have hsm : ⟪Am j, s • y⟫_ℝ = s * ⟪Am j, y⟫_ℝ := real_inner_smul_right _ _ _
    rw [hsm]
    exact mul_le_mul_of_nonneg_left (hy j) hs.le
  · intro h
    refine ⟨s⁻¹ • x, fun j => ?_, by
      show s • s⁻¹ • x = x
      rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]⟩
    have he : ⟪Am j, s⁻¹ • x⟫_ℝ = s⁻¹ * ⟪Am j, x⟫_ℝ := real_inner_smul_right _ _ _
    rw [he]
    have hj := h j
    have hinv : (0:ℝ) < s⁻¹ := inv_pos.2 hs
    calc s⁻¹ * ⟪Am j, x⟫_ℝ ≤ s⁻¹ * (s * bv j) := mul_le_mul_of_nonneg_left hj hinv.le
      _ = bv j := by field_simp

/-- Re-indexing a half-space system along an equivalence does not change its body. -/
theorem body_comp_equiv {ι ι' : Type*} (e : ι ≃ ι') (Am : ι → Space n) (bv : ι → ℝ) :
    Arlib.Polytope.body (fun k => Am (e.symm k)) (fun k => bv (e.symm k))
      = Arlib.Polytope.body Am bv := by
  ext x
  constructor
  · intro h j; simpa using h (e j)
  · intro h k; exact h _

/-! ## The canonical description -/

/-- **The canonical facet normals**, indexed by `Fin (Nat.card (FacetIndex D))`. -/
noncomputable def canonNormal (atoms : A → LinAtom n) {D : DNF A}
    (i : {c : Cube A // c ∈ D}) (k : Fin (Nat.card (FacetIndex D))) : Space n :=
  facetAm atoms i ((facetEquiv D).symm k)

/-- **The canonical facet offsets** at dilation `10^ρ`. -/
noncomputable def canonOffset (atoms : A → LinAtom n) {D : DNF A} (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) (k : Fin (Nat.card (FacetIndex D))) : ℝ :=
  latticeScale ρ * facetBv atoms i ((facetEquiv D).symm k)

/-- **The canonical description is exact.**  Not a containment: the described body is
*equal* to the dilated region.  This is what makes both `hdil` and `hDbody` free. -/
theorem body_canon_eq (atoms : A → LinAtom n) {D : DNF A} (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) (hi : Cube.IsPositive i.val) :
    Arlib.Polytope.body (canonNormal atoms i) (canonOffset atoms ρ i)
      = latticeScale ρ • region (fun a => (atoms a).halfspace) i.val := by
  rw [region_eq_body_facet atoms i hi, smul_body _ _ (latticeScale_pos ρ)]
  exact body_comp_equiv (facetEquiv D) (facetAm atoms i)
    (fun j => latticeScale ρ * facetBv atoms i j)

/-- **`Ttc.ttc_volume_endToEnd`'s `hdil`, canonically.** -/
theorem hdil_canonical (atoms : A → LinAtom n) {D : DNF A} (ρ : ℤ)
    (isPositive : DNF.IsPositive D) (i : {c : Cube A // c ∈ D}) :
    latticeScale ρ • region (fun a => (atoms a).halfspace) i.val
      ⊆ Arlib.Polytope.body (canonNormal atoms i) (canonOffset atoms ρ i) :=
  (body_canon_eq atoms ρ i (isPositive _ i.2)).symm.subset

/-- **`Ttc.ttc_volume_endToEnd`'s `Dm`, canonically**: the diameter of the dilated
region.  Because the canonical body *is* the dilated region, there is no gap between
"the described body" and "the region" for the diameter to have to cover. -/
noncomputable def canonDiam (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) : ℝ :=
  Metric.diam (latticeScale ρ • region M i.val)

/-- The dilated region of a cube of a DNF of `φ` is bounded whenever `Sol(F)` is —
the capstone's `hbdd`. -/
theorem isBounded_smul_region {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (isDNF : IsDNFOf D φ) (hbdd : Bornology.IsBounded (sol M φ)) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) :
    Bornology.IsBounded (latticeScale ρ • region M i.val) :=
  (hbdd.subset (region_subset_sol isDNF i.2)).smul₀ _

/-- **`Ttc.ttc_volume_endToEnd`'s `hDbody`, canonically** — proved from `hbdd`, which
the capstone already binds. -/
theorem hDbody_canonical {atoms : A → LinAtom n} {φ : BForm A} {D : DNF A}
    (isDNF : IsDNFOf D φ) (isPositive : DNF.IsPositive D)
    (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ)) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) :
    ∀ x ∈ Arlib.Polytope.body (canonNormal atoms i) (canonOffset atoms ρ i),
      ∀ y ∈ Arlib.Polytope.body (canonNormal atoms i) (canonOffset atoms ρ i),
      dist x y ≤ canonDiam (fun a => (atoms a).halfspace) D ρ i := by
  intro x hx y hy
  rw [body_canon_eq atoms ρ i (isPositive _ i.2)] at hx hy
  exact Metric.dist_le_diam_of_mem (isBounded_smul_region isDNF hbdd ρ i) hx hy

/-! ## The payoff -/

/-- **`Ttc.ttc_volume_endToEnd` with the linear description computed, not assumed.**

All nine description binders — `Jt`, `[Fintype Jt]`, `Am`, `bv`, `hdil`, `rfac`,
`hr1`, `hcard`, `Dm`, `hDbody` — are gone.  In their place stand the *canonical*
values, which for a **positive** DNF are forced:

* `Jt := Fin (Nat.card (FacetIndex (toDNF φ)))` — the capstone's own facet index,
  enumerated so it lands in `Type 0`;
* `Am := Ttc.canonNormal atoms` and `bv := Ttc.canonOffset atoms (P.precision γ̂)` —
  the atoms' coefficient vectors and (dilated) bounds, with `⟪0, x⟫ ≤ 0` in the rows
  belonging to other cubes.  `Ttc.body_canon_eq` proves the padded system cuts out
  `10^ρ · region M i` **exactly**, so `hdil` is an equality read as a containment;
* `rfac := Nat.card (FacetIndex (toDNF φ))` — the capstone's existing binder `hr`
  supplies `hr1` and `Fintype.card_fin` supplies `hcard`, with no slack;
* `Dm := Ttc.canonDiam M (toDNF φ) (P.precision γ̂)`, the **diameter** of the dilated
  region.  Because the description is exact there is no gap between the described body
  and the region, so `hDbody` follows from the capstone's `hbdd` alone.

Every other binder of `Ttc.ttc_volume_endToEnd` is kept verbatim, and the conclusion is
its conclusion with the canonical values substituted — nothing is weakened.

**Cost, stated plainly.**  This removes an *assumption*, not a cost.  The description
is exponential in `n` in general: `Ttc.toDNF` can return exponentially many cubes, so
`Nat.card (FacetIndex (toDNF φ))` — hence the row count of every cube's system, since
every cube carries the whole facet index as its padded row set — is exponential in the
input size in the worst case.  And, exactly as in `Ttc.ttc_volume_endToEnd`, the volume
oracle is hit-and-miss Monte Carlo and the ball walk's step count is exponential in
`n`: the running-time conjunct is the *charged* cost of `alg:ttc`'s loops, not a
polynomial-time claim. -/
theorem ttc_volume_endToEnd_canonical
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε δ hε0 hε1 hn hm hr)
    (hlen : ((toDNF φ).length : ℝ) ≤ P.m)
    (hbdd : Bornology.IsBounded (sol M φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (big : ∀ c ∈ mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime,
      (1 - P.epsPrime) * P.thresh / 8
        ≤ ∑ s, rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime
              (Nat.card (FacetIndex (toDNF φ)) : ℝ)
              (canonNormal atoms) (canonOffset atoms (P.precision gammaHat)) cen gammaHat
              (canonDiam M (toDNF φ) (P.precision gammaHat)))
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) s) :
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime
              (Nat.card (FacetIndex (toDNF φ)) : ℝ)
              (canonNormal atoms) (canonOffset atoms (P.precision gammaHat)) cen gammaHat
              (canonDiam M (toDNF φ) (P.precision gammaHat)))
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c))
          {t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ |
            ttcOutput P (coveredOracles M φ (P.precision gammaHat)
                (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c))
                toDNF (P.precision gammaHat) φ t
              ∈ relErr ε (volSol M φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = P.thresh →
      Terminates P (coveredOracles M φ (P.precision gammaHat)
          (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) t) (toDNF φ) →
      runCost P (coveredOracles M φ (P.precision gammaHat)
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) t)
          cVol cSample (P.precision gammaHat) (toDNF φ)
        ≤ (toDNF φ).length * (cVol + cSample * thr)) := by
  subst M_eq
  exact ttc_volume_endToEnd atoms φ ε δ hε0 hε1 hδ0 hδ1 hn _ rfl toDNF isDNF isPositive
    hm hr P hP hlen hbdd hcoeff cen gammaHat hgammaHat ball_subset
    (Fin (Nat.card (FacetIndex (toDNF φ)))) (canonNormal atoms)
    (canonOffset atoms (P.precision gammaHat))
    (fun i => hdil_canonical atoms (P.precision gammaHat) isPositive i)
    (Nat.card (FacetIndex (toDNF φ)) : ℝ) (by exact_mod_cast hr)
    (by rw [Fintype.card_fin])
    (canonDiam (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat))
    (hDbody_canonical isDNF isPositive hbdd (P.precision gammaHat))
    big

/-- **The end-to-end sampling law at the canonical description.**  Definitionally the
`Ttc.e2eSampD …` that appears in `Ttc.ttc_volume_endToEnd_canonical`; named so that the
non-vacuity statement below can mention it without repeating the description. -/
noncomputable def canonSampD (atoms : A → LinAtom n) (D : DNF A) (P : Params)
    (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ) : Cube A → Space n → ℝ :=
  e2eSampD (fun a => (atoms a).halfspace) D (P.precision gammaHat) P.epsPrime
    (Nat.card (FacetIndex D) : ℝ) (canonNormal atoms) (canonOffset atoms (P.precision gammaHat))
    cen gammaHat (canonDiam (fun a => (atoms a).halfspace) D (P.precision gammaHat))

/-! ## Non-vacuity: the box, with the canonical description

`Ttc.Box.ttc_volume_endToEnd_box_at` (`Exec/EndToEnd`) instantiates
`Ttc.ttc_volume_endToEnd` on the box `[0,c]ⁿ` using the box's *hand-written* linear
description (`Ttc.Box.bxNormal`, `Ttc.Box.bxOffsetOf`, `Ttc.Box.bfac`,
`Ttc.Box.bxDm`).  What follows does the same for
`Ttc.ttc_volume_endToEnd_canonical`, where there is nothing to hand-write: the
description is `Ttc.canonNormal`/`Ttc.canonOffset`/`Ttc.canonDiam` at the box's own atoms.
-/

namespace Box

open MeasureTheory Set

variable (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)

/-- **The box's ball-walk sampler's discrete law, at the *canonical* description.**
`Ttc.Box.bxSampD` with `Ttc.Box.bxNormal`/`Ttc.Box.bxOffsetOf`/`Ttc.Box.bfac`/
`Ttc.Box.bxDm` replaced by the description `Ttc.ttc_volume_endToEnd_canonical`
computes. -/
noncomputable def bxCanonSampD : Cube (Fin n ⊕ Fin n) → Space n → ℝ :=
  e2eSampD (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
    (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
    (parS n hn ε δ hε0 hε1).epsPrime
    (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn))) : ℝ)
    (canonNormal (boxAtoms n (sideS n hn ε δ hε0 hε1)))
    (canonOffset (boxAtoms n (sideS n hn ε δ hε0 hε1)) (rhoS n hn ε δ hε0 hε1))
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
    (canonDiam (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1))

/-- **The box's ball-walk sampler at the canonical description**, with no accuracy
assumption: `Ttc.e2eSampler`'s inputs are all discharged by this file's lemmas. -/
noncomputable def bxCanonSampler :
    KV97Sampler (Fin n ⊕ Fin n) n
      (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (bxCanonSampD n hn ε δ hε0 hε1) :=
  e2eSampler hn (parS_epsPrime_pos (δ := δ) hn hε0 hε1)
    (Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
    (canonNormal (boxAtoms n (sideS n hn ε δ hε0 hε1)))
    (canonOffset (boxAtoms n (sideS n hn ε δ hε0 hε1)) (rhoS n hn ε δ hε0 hε1))
    (fun i => hdil_canonical (boxAtoms n (sideS n hn ε δ hε0 hε1))
      (rhoS n hn ε δ hε0 hε1) (toDNF_isPositive (boxForm_isPositive hn)) i)
    (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn))) : ℝ)
    (by exact_mod_cast one_le_card_facets_box n hn)
    (by rw [Fintype.card_fin])
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1)
    (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (canonDiam (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1))
    (hDbody_canonical (toDNF_isDNFOf (boxForm n hn))
      (toDNF_isPositive (boxForm_isPositive hn))
      (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn) (rhoS n hn ε δ hε0 hε1))

/-- **`eq:almostuniform` for the canonically-described box sampler** —
`Ttc.almostUniform_of_kv97Sampler` at `Ttc.Box.bxCanonSampler`.  As for
`Ttc.Box.bxSampD_almostUniform`, the only route to it is mixing. -/
theorem bxCanonSampD_almostUniform :
    AlmostUniform (bxCanonSampD n hn ε δ hε0 hε1 (boxCube n))
      (region (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) (boxCube n)
        ∩ fineLattice n (latticeScale (rhoS n hn ε δ hε0 hε1)))
      (parS n hn ε δ hε0 hε1).epsPrime :=
  almostUniform_of_kv97Sampler (bxCanonSampler n hn ε δ hε0 hε1)
    (parS_epsPrime_pos (δ := δ) hn hε0 hε1)
    (by have := parS_epsPrime_le (n := n) (δ := δ) hn hε0 hε1; linarith)
    ⟨boxCube n, mem_toDNF_boxCube n hn⟩
    (dilate_finite_box n hn ε δ hε0 hε1 ⟨boxCube n, mem_toDNF_boxCube n hn⟩)
    (dilate_nonempty_box n hn ε δ hε0 hε1 ⟨boxCube n, mem_toDNF_boxCube n hn⟩)

/-- **The rates of *any* almost-uniform sampling law sum to at least `(1−ε')·Vol_ED`
on the box.**  `Ttc.Box.sum_bxRates_ge` (`Exec/EndToEnd`) is this statement at
`Ttc.Box.bxSampD`; its proof uses the sampler only through `eq:almostuniform`, so it
is stated here over the law, and applied at `Ttc.Box.bxCanonSampD`. -/
theorem sum_rates_ge_of_almostUniform (sampD : Cube (Fin n ⊕ Fin n) → Space n → ℝ)
    (hAU : AlmostUniform (sampD (boxCube n))
      (region (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) (boxCube n)
        ∩ fineLattice n (latticeScale (rhoS n hn ε δ hε0 hε1)))
      (parS n hn ε δ hε0 hε1).epsPrime)
    (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime) :
    (1 - (parS n hn ε δ hε0 hε1).epsPrime) * volMC n hn ε δ hε0 hε1 c (boxCube n)
      ≤ ∑ s, rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
          (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
          sampD (volMC n hn ε δ hε0 hε1 c) s := by
  set c0 := sideS n hn ε δ hε0 hε1 with hc0
  set ρ := rhoS n hn ε δ hε0 hε1 with hρ
  set N := (region (fun a => (boxAtoms n c0 a).halfspace) (boxCube n)
    ∩ fineLattice n (latticeScale ρ)).ncard with hNdef
  have heps1 : (parS n hn ε δ hε0 hε1).epsPrime < 1 := by
    have := parS_epsPrime_le (n := n) (δ := δ) hn hε0 hε1; linarith
  have hvpos : 0 < volMC n hn ε δ hε0 hε1 c (boxCube n) :=
    mcVol_pos (fun a => (boxAtoms n c0 a).halfspace) (Ttc.toDNF (boxForm n hn))
      (cenMC n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1) heps1
      (ball_subset_bxOf n c0 hn)
      (volume_region_ne_top_of_isBounded (toDNF_isDNFOf (boxForm n hn))
        (isBounded_sol_bxOf n c0 hn))
      hc (boxCube n) (mem_toDNF_boxCube n hn)
  have hL : latticeCount (fun a => (boxAtoms n c0 a).halfspace) (boxForm n hn) ρ = N := by
    rw [hNdef, region_eq_bxOf n c0 hn (mem_toDNF_boxCube n hn),
      latticeCount_eq_ncard n c0 hn ρ]
  have hNpos : 0 < N := by
    rw [hNdef, region_eq_bxOf n c0 hn (mem_toDNF_boxCube n hn)]
    exact ncard_lat_pos n (sideS_pos hn hε0 hε1).le ρ
  have key : ∀ s, (1 - (parS n hn ε δ hε0 hε1).epsPrime) / (N : ℝ)
      * volMC n hn ε δ hε0 hε1 c (boxCube n)
      ≤ rates (fun a => (boxAtoms n c0 a).halfspace) (boxForm n hn)
          (Ttc.toDNF (boxForm n hn)) ρ sampD (volMC n hn ε δ hε0 hε1 c) s := by
    intro s
    have hspec := cubeAt_spec (toDNF_isDNFOf (boxForm n hn))
      (hasLatticeEnum_bxOf n c0 hn ρ) s
    have hcu : cubeAt (fun a => (boxAtoms n c0 a).halfspace) (boxForm n hn)
        (Ttc.toDNF (boxForm n hn)) ρ s = boxCube n := by
      simpa only [toDNF_boxForm hn, boxDNF, List.mem_singleton] using hspec.1
    have hmem : latticeEnum (fun a => (boxAtoms n c0 a).halfspace) (boxForm n hn) ρ s
        ∈ region (fun a => (boxAtoms n c0 a).halfspace) (boxCube n)
          ∩ fineLattice n (latticeScale ρ) :=
      ⟨hcu ▸ hspec.2, (latticeEnum_mem (hasLatticeEnum_bxOf n c0 hn ρ) s).2⟩
    simp only [rates, hcu]
    exact mul_le_mul_of_nonneg_right (hAU.lower hmem) hvpos.le
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun s _ => key s))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hL]
  have hNne : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
  field_simp

/-- **`Ttc.ttc_volume_endToEnd_canonical`'s `big`, for the box**, at every coin on
which the volume oracle got the volume right.  The route to the rates is
`eq:almostuniform` for the *canonically described* ball walk. -/
theorem big_canon_box (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime) :
    (1 - (parS n hn ε δ hε0 hε1).epsPrime) * (parS n hn ε δ hε0 hε1).thresh / 8
      ≤ ∑ s, rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
          (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
          (bxCanonSampD n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) s := by
  refine le_trans ?_ (sum_rates_ge_of_almostUniform n hn ε δ hε0 hε1 _
    (bxCanonSampD_almostUniform n hn ε δ hε0 hε1) c hc)
  have heps := parS_epsPrime_le (n := n) (δ := δ) hn hε0 hε1
  have hlo := (mcVol_mem_relErr (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
    (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
    (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime hc
    (boxCube n) (mem_toDNF_boxCube n hn)).1
  rw [region_eq_bxOf n (sideS n hn ε δ hε0 hε1) hn (mem_toDNF_boxCube n hn)] at hlo
  have hthr := thresh_div_eight_le_epsPrime_volumeS n hn ε δ hε0 hε1 hδ0 hδ1
  have hstep : (parS n hn ε δ hε0 hε1).thresh / 8
      ≤ volMC n hn ε δ hε0 hε1 c (boxCube n) := le_trans hthr hlo
  nlinarith [hstep, heps]

/-- **The canonically-described rates are strictly positive on the box**, at every coin
the volume oracle got right.  So this witness is not the collapsed `θ ≡ 0` that would
satisfy `theta_eq` vacuously and fail `big`. -/
theorem bxCanonRates_pos (c : ℕ → Space n)
    (hc : c ∈ mcGood (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (parS n hn ε δ hε0 hε1).deltaPrime)
    (s : Fin (latticeCount (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (boxForm n hn) (rhoS n hn ε δ hε0 hε1))) :
    0 < rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
      (bxCanonSampD n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) s := by
  have heps1 : (parS n hn ε δ hε0 hε1).epsPrime < 1 := by
    have := parS_epsPrime_le (n := n) (δ := δ) hn hε0 hε1; linarith
  refine rates_pos_of_almostUniform (toDNF_isDNFOf (boxForm n hn))
    (hasLatticeEnum_bxOf n (sideS n hn ε δ hε0 hε1) hn (rhoS n hn ε δ hε0 hε1))
    (mcVol_pos (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (cenMC n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1) heps1
      (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
      (volume_region_ne_top_of_isBounded (toDNF_isDNFOf (boxForm n hn))
        (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn))
      hc)
    heps1 (fun i hi => ?_) s
  have hib : i = boxCube n := by
    simpa only [toDNF_boxForm hn, boxDNF, List.mem_singleton] using hi
  subst hib
  exact bxCanonSampD_almostUniform n hn ε δ hε0 hε1

/-- **`Ttc.ttc_volume_endToEnd_canonical`'s hypotheses are satisfiable, at every
`(ε, δ) ∈ (0,1]²`.**

The box `[0,c]ⁿ` with `c = max 1 Thresh(ε, δ)`, carrying **no oracle and no supplied
linear description**: the volume estimates are the Monte-Carlo oracle's own output, the
rates are `Ttc.rates` built on them, the sampler is the lazy ball walk of
`Ttc.kv97SamplerOfBody`, and the polytope description is `Ttc.canonNormal`/`Ttc.canonOffset`/
`Ttc.canonDiam` — read off the box's atoms.  The only inputs are the box's geometry. -/
theorem ttc_volume_endToEnd_canonical_box_at (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
            (bxCanonSampD n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
          {t : ℕ → Fin (latticeCount
              (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
              (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ |
            ttcOutput (parS n hn ε δ hε0 hε1)
                (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
                Ttc.toDNF (rhoS n hn ε δ hε0 hε1) (boxForm n hn) t
              ∈ relErr ε (volSol
                  (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn))}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (latticeCount
        (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = (parS n hn ε δ hε0 hε1).thresh →
      Terminates (parS n hn ε δ hε0 hε1)
          (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) t)
          (Ttc.toDNF (boxForm n hn)) →
      runCost (parS n hn ε δ hε0 hε1)
          (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c) t)
          cVol cSample (rhoS n hn ε δ hε0 hε1) (Ttc.toDNF (boxForm n hn))
        ≤ (Ttc.toDNF (boxForm n hn)).length * (cVol + cSample * thr)) :=
  ttc_volume_endToEnd_canonical (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxForm n hn) ε δ
    hε0 hε1 hδ0 hδ1 hn
    (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace) rfl Ttc.toDNF
    (toDNF_isDNFOf _) (toDNF_isPositive (boxForm_isPositive hn))
    (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn)
    (parS n hn ε δ hε0 hε1) rfl (hlen_box n hn ε δ hε0 hε1)
    (isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (coeff_ne_zero_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1)
    (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (big_canon_box n hn ε δ hε0 hε1 hδ0 hδ1)

/-- The box's canonical law is `Ttc.canonSampD` at the box's data. -/
theorem bxCanonSampD_eq :
    bxCanonSampD n hn ε δ hε0 hε1
      = canonSampD (boxAtoms n (sideS n hn ε δ hε0 hε1)) (Ttc.toDNF (boxForm n hn))
          (parS n hn ε δ hε0 hε1) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) := rfl

/-! ### The pair, and the guarantee is a real number

One witness cannot distinguish "the hypotheses are satisfiable" from "the hypotheses
force one accuracy pair", so `Ttc.Box.AtParamsCanon` packages the conclusion of
`Ttc.ttc_volume_endToEnd_canonical` over the data it is stated about, with `(ε, δ)`
exposed.  It asserts nothing that is not proved: `Ttc.Box.atParamsCanon_of` establishes
it at **every** `(ε, δ) ∈ (0,1]²`. -/

/-- **`Ttc.ttc_volume_endToEnd_canonical`'s conclusion, with `(ε, δ)` exposed.**

Unlike `Ttc.Box.AtParamsE2E`, the sampling law is not existentially quantified: it is
`Ttc.canonSampD`, the law forced by the **canonical** linear description of the input
polytopes.  Six of the theorem's hypotheses travel with it — the parameter block really
is at the stated accuracy, the DNF is positive, the solution set is bounded, `γ̂ > 0`,
the **sampler exists** at these parameters, and the rates are **strictly positive** at
every coin the volume oracle got right — so a degenerate instance (an uninhabited
`Ttc.KV97Sampler`, or the collapsed `θ ≡ 0` that satisfies `theta_eq` vacuously) cannot
satisfy it. -/
def AtParamsCanon (n : ℕ) (ε δ : ℝ) : Prop :=
  ∃ (atoms : (Fin n ⊕ Fin n) → LinAtom n) (φ : BForm (Fin n ⊕ Fin n)) (P : Params)
      (gammaHat : ℝ)
      (cen : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF φ} → Space n),
    0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧ P.ε = ε ∧ P.δ = δ ∧ P.n = n ∧ 0 < gammaHat ∧
    DNF.IsPositive (Ttc.toDNF φ) ∧
    Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ) ∧
    Nonempty (KV97Sampler (Fin n ⊕ Fin n) n (fun a => (atoms a).halfspace) (Ttc.toDNF φ)
      (P.precision gammaHat) P.epsPrime
      (canonSampD atoms (Ttc.toDNF φ) P cen gammaHat)) ∧
    (∀ c ∈ mcGood (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
        P.epsPrime P.deltaPrime,
      ∀ s, 0 < rates (fun a => (atoms a).halfspace) φ (Ttc.toDNF φ) (P.precision gammaHat)
        (canonSampD atoms (Ttc.toDNF φ) P cen gammaHat)
        (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
          P.epsPrime P.deltaPrime c) s) ∧
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (rates (fun a => (atoms a).halfspace) φ (Ttc.toDNF φ)
            (P.precision gammaHat) (canonSampD atoms (Ttc.toDNF φ) P cen gammaHat)
            (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
              P.epsPrime P.deltaPrime c))
          {t : ℕ → Fin (latticeCount (fun a => (atoms a).halfspace) φ
              (P.precision gammaHat)) → ℕ |
            ttcOutput P (coveredOracles (fun a => (atoms a).halfspace) φ
                (P.precision gammaHat)
                (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
                  P.epsPrime P.deltaPrime c))
                Ttc.toDNF (P.precision gammaHat) φ t
              ∈ relErr ε (volSol (fun a => (atoms a).halfspace) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (latticeCount (fun a => (atoms a).halfspace) φ
        (P.precision gammaHat)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = P.thresh →
      Terminates P (coveredOracles (fun a => (atoms a).halfspace) φ (P.precision gammaHat)
          (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
            P.epsPrime P.deltaPrime c) t) (Ttc.toDNF φ) →
      runCost P (coveredOracles (fun a => (atoms a).halfspace) φ (P.precision gammaHat)
            (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
              P.epsPrime P.deltaPrime c) t)
          cVol cSample (P.precision gammaHat) (Ttc.toDNF φ)
        ≤ (Ttc.toDNF φ).length * (cVol + cSample * thr))

/-- **The description-free capstone is instantiable at every accuracy pair in
`(0,1]²`.**  The witness is the box, its Monte-Carlo volume oracle, its constructed
rates, and the lazy ball walk run on the **canonical** polytope description. -/
theorem atParamsCanon_of (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : AtParamsCanon n ε δ := by
  obtain ⟨hacc, hrun⟩ := ttc_volume_endToEnd_canonical_box_at n hn ε δ hε0 hε1 hδ0 hδ1
  exact ⟨boxAtoms n (sideS n hn ε δ hε0 hε1), boxForm n hn, parS n hn ε δ hε0 hε1,
    gamS n hn ε δ hε0 hε1, cenMC n hn ε δ hε0 hε1,
    hε0, hε1, hδ0, hδ1, rfl, rfl, rfl, gamS_pos hn hε0 hε1,
    toDNF_isPositive (boxForm_isPositive hn),
    isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn,
    ⟨bxCanonSampler n hn ε δ hε0 hε1⟩,
    fun c hc s => bxCanonRates_pos n hn ε δ hε0 hε1 c hc s, hacc, hrun⟩

/-- **The guarantee is a genuine number, not `ENNReal.toReal ⊤ = 0`.**  Wherever the
budget `1 − δ − δ/4` is positive, the bound itself forces the integral to be finite and
nonzero.  Nothing is assumed here — it is read off the theorem. -/
theorem canon_box_lintegral_pos_ne_top (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hbudget : 0 < 1 - δ - δ / 4) (I : ENNReal)
    (hI : I = ∫⁻ c, trajLaw (rates
            (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
            (bxCanonSampD n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
          {t : ℕ → Fin (latticeCount
              (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
              (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ |
            ttcOutput (parS n hn ε δ hε0 hε1)
                (coveredOracles (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
                Ttc.toDNF (rhoS n hn ε δ hε0 hε1) (boxForm n hn) t
              ∈ relErr ε (volSol
                  (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn))}
        ∂(MonteCarlo.coins n)) :
    0 < I ∧ I ≠ ⊤ := by
  have hacc := (ttc_volume_endToEnd_canonical_box_at n hn ε δ hε0 hε1 hδ0 hδ1).1
  rw [← hI] at hacc
  have hpos : 0 < I.toReal := lt_of_lt_of_le hbudget hacc
  exact ⟨(ENNReal.toReal_pos_iff.1 hpos).1, (ENNReal.toReal_pos_iff.1 hpos).2.ne⟩

/-- **`ε` and `δ` are not forced, and both instances are informative.**

`Ttc.Box.ttc_volume_endToEnd_canonical_box_at` at two *different* accuracy pairs, both
strictly inside `(0,1)`, with the achieved guarantee written as a numeral and proved
strictly positive: `3/8` at `(1/2, 1/2)` and `11/16` at `(1/4, 1/4)`.  Both conclusions
are therefore genuine positive lower bounds on a probability.  (Above `δ = 4/5` the
budget `1 − δ − δ/4` is not positive; that corner certifies nothing and is not
claimed.) -/
theorem exists_two_ttc_volume_endToEnd_canonical_instances (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε₁ δ₁ ε₂ δ₂ : ℝ,
      AtParamsCanon n ε₁ δ₁ ∧ AtParamsCanon n ε₂ δ₂ ∧
      ε₁ ≠ ε₂ ∧ δ₁ ≠ δ₂ ∧
      (0 < ε₁ ∧ ε₁ < 1) ∧ (0 < δ₁ ∧ δ₁ < 1) ∧
      (0 < ε₂ ∧ ε₂ < 1) ∧ (0 < δ₂ ∧ δ₂ < 1) ∧
      1 - δ₁ - δ₁ / 4 = 3 / 8 ∧ 1 - δ₂ - δ₂ / 4 = 11 / 16 ∧
      (0 : ℝ) < 3 / 8 ∧ (0 : ℝ) < 11 / 16 ∧
      0 < 1 - δ₁ - δ₁ / 4 ∧ 0 < 1 - δ₂ - δ₂ / 4 :=
  ⟨1/2, 1/2, 1/4, 1/4,
    atParamsCanon_of n hn (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    atParamsCanon_of n hn (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    by norm_num, by norm_num, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Box

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

-- the inner product, and the canonical rows
#print axioms mem_halfspace_iff_inner
#print axioms lit_holds_iff_inner
#print axioms facetEquiv
#print axioms facetAm
#print axioms facetBv
#print axioms facetAm_of_eq
#print axioms facetAm_of_ne
#print axioms facetBv_of_eq
#print axioms facetBv_of_ne
#print axioms region_eq_body_facet

-- dilation, re-indexing, and the canonical description
#print axioms smul_body
#print axioms body_comp_equiv
#print axioms canonNormal
#print axioms canonOffset
#print axioms body_canon_eq
#print axioms hdil_canonical
#print axioms canonDiam
#print axioms isBounded_smul_region
#print axioms hDbody_canonical

-- the payoff
#print axioms ttc_volume_endToEnd_canonical
#print axioms canonSampD

-- non-vacuity on the box
#print axioms Box.bxCanonSampD
#print axioms Box.bxCanonSampler
#print axioms Box.bxCanonSampD_almostUniform
#print axioms Box.sum_rates_ge_of_almostUniform
#print axioms Box.big_canon_box
#print axioms Box.bxCanonRates_pos
#print axioms Box.ttc_volume_endToEnd_canonical_box_at
#print axioms Box.bxCanonSampD_eq
#print axioms Box.AtParamsCanon
#print axioms Box.atParamsCanon_of
#print axioms Box.canon_box_lintegral_pos_ne_top
#print axioms Box.exists_two_ttc_volume_endToEnd_canonical_instances

end Ttc
