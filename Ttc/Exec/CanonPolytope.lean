/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.EndToEnd

/-!
# `Exec/CanonPolytope`: the linear description of the dilated regions, constructed

`Ttc.ttc_volume_endToEnd` (`Exec/EndToEnd`) still carries ten binders that describe
the input polytopes:

```lean
Jt : Type
[Fintype Jt]
Am : {c : Cube A // c ∈ toDNF φ} → Jt → Space n
bv : {c : Cube A // c ∈ toDNF φ} → Jt → ℝ
hdil : ∀ i, latticeScale (P.precision γ̂) • region M i.val ⊆ Arlib.Polytope.body (Am i) (bv i)
rfac : ℝ ,  hr1 : 1 ≤ rfac ,  hcard : (Fintype.card Jt : ℝ) ≤ rfac
Dm : {c : Cube A // c ∈ toDNF φ} → ℝ
hDbody : ∀ i, ∀ x ∈ body (Am i) (bv i), ∀ y ∈ body (Am i) (bv i), dist x y ≤ Dm i
```

All ten are **redundant**: `M_eq : M = fun a => (atoms a).halfspace` already says each
`region M c` *is* a polytope, presented by the rows `atoms l` for `l ∈ c`.  This file
builds that presentation canonically and discharges the ten, giving
`Ttc.ttc_volume_endToEnd_canon` — `Ttc.ttc_volume_endToEnd` minus exactly those ten
binders, with the same conclusion at the canonical values.

## The construction

The rows are the facets of the *whole* DNF, one per literal of every cube; the rows
belonging to other cubes are switched off by zeroing both sides.  Writing
`j := facetOf D k` for the facet of row `k`:

```
canonAm atoms D i k = if j.1 = i then coeff (atoms j.2.val.atom) else 0
canonBv atoms D s i k = if j.1 = i then s * bound (atoms j.2.val.atom) else 0
```

A switched-off row reads `⟪0, x⟫ = 0 ≤ 0`, true for every `x`
(`Ttc.canon_row_of_ne`), so it constrains neither `Arlib.Polytope.body` nor
`Arlib.Polytope.inflate`.

`Jt := Fin (Nat.card (FacetIndex (toDNF φ)))` rather than `FacetIndex (toDNF φ)`
itself for a purely universe-theoretic reason: the sampler's row index is declared
`Jt : Type` (universe `0`) throughout `Sampler/Construct` and `Exec/EndToEnd`, while
`FacetIndex D` lives in the universe of the atom type `A : Type*`.  `Ttc.facetOf`
is the enumeration `Fin (Nat.card (FacetIndex D)) ≃ FacetIndex D` supplied by
`Ttc.instFiniteFacetIndex`; keeping it means `Ttc.ttc_volume_endToEnd_canon` retains
`ttc_volume_endToEnd`'s full generality in `A` instead of being restricted to
`A : Type`.  Nothing below depends on which bijection is chosen, and
`Fintype.card (Fin N) = N` makes `hcard` an equality.

What is proved is stronger than `hdil` asks for: an **equality**

`Ttc.canon_body_eq_smul_region : Arlib.Polytope.body (canonAm atoms D i) (canonBv atoms D s i)
  = s • region (fun a => (atoms a).halfspace) i.val`  (for `0 < s`),

so the described body is not merely a superset of the dilated region — it is that
region.  `hdil` is `le_of_eq` of it.  The facet bound is the exact facet count,
`Ttc.canonRfac D = Nat.card (FacetIndex D)`, and the diameter is the honest one,
`Ttc.canonDm M D ρ i = Metric.diam (latticeScale ρ • region M i.val)`, finite because
`hbdd : Bornology.IsBounded (sol M φ)` is already a binder.

## Non-vacuity

`Ttc.ttc_volume_endToEnd_canon` would be worthless if no tuple of inputs met its
binders, so §8 exhibits some: the box `[0,c]ⁿ` with `c = max 1 Thresh(ε, δ)`, no
oracle and no supplied description, at **two** different accuracy pairs
(`Ttc.Box.exists_two_ttc_volume_endToEnd_canon_instances`).  The achieved probability
is proved strictly positive and finite inside the statement, not merely bounded below
by a possibly-negative budget.

## Costs

No cost model changes: this file only substitutes values for binders of
`Ttc.ttc_volume_endToEnd`, whose cost conclusion
`runCost … ≤ (toDNF φ).length * (cVol + cSample * thresh)` — `alg:ttc`'s `m·(C_vol +
C_sample·Thresh)` — is reproduced verbatim in `Ttc.ttc_volume_endToEnd_canon`.  The
facet count `r` that `Ttc.Params.gamma` and `Ttc.Params.thresh` read is the same
`Nat.card (FacetIndex (toDNF φ))` the parameter block `Ttc.ttcParams` already stores,
so `rfac := Ttc.canonRfac (toDNF φ)` introduces no slack: `hcard` holds with equality.

What the construction *does* cost is size, and it is not small.  Every cube's system
is indexed by the facets of the **whole** DNF, so each of the `m` systems has
`Nat.card (FacetIndex (toDNF φ))` rows, of which all but that cube's own are padding;
and `toDNF` can return exponentially many cubes, so both `m` and the row count are
exponential in the input size in the worst case.  Constructing the description
removes an *assumption*, not a cost.

## What is *not* claimed

Nothing here says the presentation is irredundant, or that the polytope is bounded
beyond what `hbdd` gives; and, as in `Ttc.ttc_volume_endToEnd`, the sampler is a
finite-time lazy ball-walk iterate meeting `Ttc.KV97Sampler.law_tv`, not a claim of
exact stationarity.  The non-vacuity witness of §8 is a **single-cube** DNF, so
`hlen`, the `m`-way union bound and the per-cube error composition are not exercised
beyond arity one (`Ttc.TwoCube.ttc_volume_final_two_cube`, `Witness/TwoCube`, is the
two-cube witness for the downstream capstone).
-/

namespace Ttc

open MeasureTheory Set Pointwise
open scoped InnerProductSpace

variable {A : Type*} {n : ℕ}

/-! ## 1. The canonical linear system -/

section System

variable {atoms : A → LinAtom n} {D : DNF A}

theorem canonAm_self {i : {c : Cube A // c ∈ D}} {k : Fin (Nat.card (FacetIndex D))}
    (h : (facetOf D k).1 = i) :
    canonAm atoms D i k = WithLp.toLp 2 (atoms (facetOf D k).2.val.atom).coeff := if_pos h

theorem canonAm_of_ne {i : {c : Cube A // c ∈ D}} {k : Fin (Nat.card (FacetIndex D))}
    (h : ¬ (facetOf D k).1 = i) : canonAm atoms D i k = 0 := if_neg h

theorem canonBv_self {s : ℝ} {i : {c : Cube A // c ∈ D}} {k : Fin (Nat.card (FacetIndex D))}
    (h : (facetOf D k).1 = i) :
    canonBv atoms D s i k = s * (atoms (facetOf D k).2.val.atom).bound := if_pos h

theorem canonBv_of_ne {s : ℝ} {i : {c : Cube A // c ∈ D}} {k : Fin (Nat.card (FacetIndex D))}
    (h : ¬ (facetOf D k).1 = i) : canonBv atoms D s i k = 0 := if_neg h

/-- **The switched-off rows constrain nothing.**  For a row whose facet does not
belong to `i` the constraint reads `⟪0, x⟫_ℝ ≤ 0`, i.e. `0 ≤ 0`, which every `x`
satisfies — so they change neither the body nor its inflation. -/
theorem canon_row_of_ne {s : ℝ} {i : {c : Cube A // c ∈ D}}
    {k : Fin (Nat.card (FacetIndex D))} (h : ¬ (facetOf D k).1 = i) (x : Space n) :
    ⟪canonAm atoms D i k, x⟫_ℝ ≤ canonBv atoms D s i k := by
  rw [canonAm_of_ne h, canonBv_of_ne h, inner_zero_left]

/-- **Membership in the canonical body**, unfolded: only the rows of cube `i`
matter, and each reads `∑ₖ Aₖ xₖ ≤ s·b`. -/
theorem mem_canon_body_iff {s : ℝ} (i : {c : Cube A // c ∈ D}) (x : Space n) :
    x ∈ Arlib.Polytope.body (canonAm atoms D i) (canonBv atoms D s i)
      ↔ ∀ l ∈ i.val, ∑ k, (atoms l.atom).coeff k * x k ≤ s * (atoms l.atom).bound := by
  simp only [Arlib.Polytope.mem_body]
  constructor
  · intro h l hl
    have he : facetOf D ((facetOf D).symm ⟨i, ⟨l, hl⟩⟩) = ⟨i, ⟨l, hl⟩⟩ :=
      (facetOf D).apply_symm_apply _
    have hj := h ((facetOf D).symm ⟨i, ⟨l, hl⟩⟩)
    rw [canonAm_self (by rw [he]), canonBv_self (by rw [he]),
      Arlib.KV97.inner_eq_sum_coords, he] at hj
    exact hj
  · intro h k
    by_cases hik : (facetOf D k).1 = i
    · have hmem : (facetOf D k).2.val ∈ i.val := by rw [← hik]; exact (facetOf D k).2.property
      rw [canonAm_self hik, canonBv_self hik, Arlib.KV97.inner_eq_sum_coords]
      exact h _ hmem
    · exact canon_row_of_ne hik x

end System

/-! ## 2. The region of a positive cube, as a linear system -/

/-- **`Ttc.LinAtom.halfspace` is an `Arlib.Polytope` row.**  `Ttc.sum_mul_eq_inner`
(`Nonconv/BallFacet`, itself `Arlib.KV97.inner_eq_sum_coords`) already identifies
`∑ i, a i · x i` with `⟪a, x⟫_ℝ` in `Ttc.Space n`; this is that identification read on
`Ttc.LinAtom.halfspace`, i.e. the statement that an atom *is* a half-space row. -/
theorem mem_halfspace_iff_inner (a : LinAtom n) (x : Space n) :
    x ∈ a.halfspace ↔ ⟪coeffPt a.coeff, x⟫_ℝ ≤ a.bound := by
  rw [LinAtom.halfspace, Set.mem_setOf_eq, sum_mul_eq_inner]

/-- **A positive literal is a single half-space row.**  Positivity is essential: a
negated literal is the *complement* of a closed half-space, hence open, and is not a
row of any `Arlib.Polytope.body` (README, finding 5). -/
theorem lit_holds_iff_inner {atoms : A → LinAtom n} {l : Lit A} (hl : l.pos = true)
    (x : Space n) :
    l.holds (induced (fun a => (atoms a).halfspace) x)
      ↔ ⟪coeffPt (atoms l.atom).coeff, x⟫_ℝ ≤ (atoms l.atom).bound := by
  simp only [Lit.holds, hl, cond_true]
  exact mem_halfspace_iff_inner _ x

/-- **A positive cube's region is the intersection of its atoms' half-spaces.**
Positivity is what makes each literal a *closed* half-space; a negated literal would
give an open one (README, finding 5). -/
theorem mem_region_halfspace_iff (atoms : A → LinAtom n) {c : Cube A}
    (hc : Cube.IsPositive c) (y : Space n) :
    y ∈ region (fun a => (atoms a).halfspace) c
      ↔ ∀ l ∈ c, ∑ k, (atoms l.atom).coeff k * y k ≤ (atoms l.atom).bound := by
  simp only [mem_region_iff]
  constructor
  · intro h l hl
    have h1 := h l hl
    rw [Lit.holds, hc l hl, cond_true] at h1
    exact h1
  · intro h l hl
    rw [Lit.holds, hc l hl, cond_true]
    exact h l hl

/-- **The dilated region, in coordinates.**  `x ∈ s·P(c)` iff `x/s ∈ P(c)`, which for
a positive cube is `∑ₖ Aₖ xₖ ≤ s·b` for every atom of `c`. -/
theorem mem_smul_region_iff (atoms : A → LinAtom n) {c : Cube A} (hc : Cube.IsPositive c)
    {s : ℝ} (hs : 0 < s) (x : Space n) :
    x ∈ s • region (fun a => (atoms a).halfspace) c
      ↔ ∀ l ∈ c, ∑ k, (atoms l.atom).coeff k * x k ≤ s * (atoms l.atom).bound := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hs),
    mem_region_halfspace_iff atoms hc]
  have key : ∀ l : Lit A, ∑ k, (atoms l.atom).coeff k * ((s⁻¹ • x : Space n) k)
      = s⁻¹ * ∑ k, (atoms l.atom).coeff k * x k := by
    intro l
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  constructor
  · intro h l hl
    have h1 := h l hl
    rw [key l] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hs.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), one_mul] at h2
    exact h2
  · intro h l hl
    have h1 := h l hl
    rw [key l]
    have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hs.le)
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs), one_mul] at h2
    exact h2

/-! ## 3. The crux: the canonical body *is* the dilated region -/

/-- **`hdil`, with equality.**  For a positive DNF the canonical system cuts out
exactly the dilated region of each cube — not merely a superset.  This is the fact
that makes `Jt`, `Am`, `bv`, `hdil` redundant. -/
theorem canon_body_eq_smul_region (atoms : A → LinAtom n) {D : DNF A}
    (hpos : DNF.IsPositive D) {s : ℝ} (hs : 0 < s) (i : {c : Cube A // c ∈ D}) :
    Arlib.Polytope.body (canonAm atoms D i) (canonBv atoms D s i)
      = s • region (fun a => (atoms a).halfspace) i.val := by
  ext x
  rw [mem_canon_body_iff i x, mem_smul_region_iff atoms (hpos i.val i.property) hs x]

/-- **A positive cube's region *is* a polytope body** — the undilated case `s = 1` of
`Ttc.canon_body_eq_smul_region`, stated separately because it is the geometric content
on its own: with the padding rows included, and as an *equality*, the canonical system
cuts out `region M i` exactly. -/
theorem canon_body_one_eq_region (atoms : A → LinAtom n) {D : DNF A}
    (hpos : DNF.IsPositive D) (i : {c : Cube A // c ∈ D}) :
    Arlib.Polytope.body (canonAm atoms D i) (canonBv atoms D 1 i)
      = region (fun a => (atoms a).halfspace) i.val := by
  rw [canon_body_eq_smul_region atoms hpos one_pos i, one_smul]

/-- `hdil` itself, as `Ttc.ttc_volume_endToEnd` asks for it. -/
theorem canon_smul_region_subset_body (atoms : A → LinAtom n) {D : DNF A}
    (hpos : DNF.IsPositive D) {s : ℝ} (hs : 0 < s) (i : {c : Cube A // c ∈ D}) :
    s • region (fun a => (atoms a).halfspace) i.val
      ⊆ Arlib.Polytope.body (canonAm atoms D i) (canonBv atoms D s i) :=
  (canon_body_eq_smul_region atoms hpos hs i).ge

/-! ## 4. The facet bound and the diameter -/

/-- **The dilated region of a cube of a DNF of `φ` is bounded** whenever `Sol(φ)` is —
which is exactly `Ttc.ttc_volume_endToEnd`'s own binder `hbdd`.  This is what makes
`Ttc.canonDm` a finite number rather than `Metric.diam` of an unbounded set (which
Mathlib would silently return as `0`, making `hDbody` false rather than vacuous). -/
theorem isBounded_smul_region {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (isDNF : IsDNFOf D φ) (hbdd : Bornology.IsBounded (sol M φ)) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) :
    Bornology.IsBounded (latticeScale ρ • region M i.val) :=
  (isBounded_region_of_isBounded_sol isDNF hbdd i.property).smul₀ _

/-- `hDbody`, discharged: the canonical body is the dilated region
(`Ttc.canon_body_eq_smul_region`), which is bounded, so any two of its points are at
distance at most its diameter. -/
theorem canon_dist_le_canonDm (atoms : A → LinAtom n) {D : DNF A} {φ : BForm A}
    (hpos : DNF.IsPositive D) (hD : IsDNFOf D φ)
    (hbdd : Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ)) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) :
    ∀ x ∈ Arlib.Polytope.body (canonAm atoms D i) (canonBv atoms D (latticeScale ρ) i),
      ∀ y ∈ Arlib.Polytope.body (canonAm atoms D i) (canonBv atoms D (latticeScale ρ) i),
        dist x y ≤ canonDm (fun a => (atoms a).halfspace) D ρ i := by
  have heq := canon_body_eq_smul_region atoms hpos (latticeScale_pos ρ) i
  have hb : Bornology.IsBounded
      (latticeScale ρ • region (fun a => (atoms a).halfspace) i.val) :=
    isBounded_smul_region hD hbdd ρ i
  intro x hx y hy
  rw [heq] at hx hy
  exact Metric.dist_le_diam_of_mem hb hx hy

/-! ## 5. Two general facts about `Arlib.Polytope.body`

Neither is on the critical path — §3 proves the crux directly, by unfolding
membership on both sides — but both are general statements about an *arbitrary*
half-space system over an *arbitrary* index type, and together they are the reason
the padded construction of §1 is obviously harmless: dilating a system only rescales
its offsets, and re-indexing it along a bijection (here `Ttc.facetOf`) does not move
its body at all.
-/

/-- **Dilating a half-space system rescales its offsets** — and as an *equality*, for
every `0 < s`, over any index type.  `Ttc.ttc_volume_endToEnd`'s `hdil` only ever asks
for `⊆`; this says the two sides coincide. -/
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

/-- **Re-indexing a half-space system along an equivalence does not change its body.**
This is why the choice of enumeration in `Ttc.facetOf` is immaterial. -/
theorem body_comp_equiv {ι ι' : Type*} (e : ι ≃ ι') (Am : ι → Space n) (bv : ι → ℝ) :
    Arlib.Polytope.body (fun k => Am (e.symm k)) (fun k => bv (e.symm k))
      = Arlib.Polytope.body Am bv := by
  ext x
  constructor
  · intro h j; simpa using h (e j)
  · intro h k; exact h _

/-! ## 6. The capstone, with the ten binders gone -/

/-- **`Ttc.ttc_volume_endToEnd` with the linear description of the input polytopes
constructed.**

Exactly `Ttc.ttc_volume_endToEnd` minus its ten polytope-description binders `Jt`,
`[Fintype Jt]`, `Am`, `bv`, `hdil`, `rfac`, `hr1`, `hcard`, `Dm`, `hDbody`; every
surviving binder is one that theorem already had, and the conclusion is that
theorem's conclusion at the canonical values

```
Jt := Fin (Nat.card (FacetIndex (toDNF φ)))
Am := canonAm atoms (toDNF φ)
bv := canonBv atoms (toDNF φ) (latticeScale (P.precision gammaHat))
rfac := canonRfac (toDNF φ)
Dm := canonDm M (toDNF φ) (P.precision gammaHat)
```

None of the ten is replaced by a new hypothesis: `hdil` follows from
`M_eq` and `isPositive` (indeed with equality, `Ttc.canon_body_eq_smul_region`),
`hr1`/`hcard` from `hr` and the exactness of the facet count, and `hDbody` from
`hbdd` and `isDNF`.

**Costs.**  Unchanged from `Ttc.ttc_volume_endToEnd`, and quoted here so the result
is auditable on its own: the guarantee is `1 − δ − δ/4` on the accuracy event
(the extra `δ/4` is the Monte-Carlo volume oracle's failure probability, already
integrated out), and the run-cost bound is
`runCost … ≤ (toDNF φ).length * (cVol + cSample * Thresh)` with `Thresh = P.thresh`,
i.e. `alg:ttc`'s `m·(C_vol + C_sample·Thresh)`; `P = ttcParams (toDNF φ) n ε δ …` fixes
`η = ε/8`, `ε' = ε/12`, `δ' = δ/(4m)`, `m = Nat.card {c // c ∈ toDNF φ}` and
`r = Nat.card (FacetIndex (toDNF φ))`, and the lattice precision is
`ρ = P.precision gammaHat = ⌈log₁₀(γ/γ̂)⌉`.

**Scope.**  As in `Ttc.ttc_volume_endToEnd`: the sampler is a lazy ball-walk iterate
from a warm start on the inscribed ball, meeting `Ttc.KV97Sampler.law_tv`; no
accuracy assumption about it is made, and no claim of exact stationarity is made
either.  `big` remains a genuine regime condition on the instance. -/
theorem ttc_volume_endToEnd_canon
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
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime (canonRfac (toDNF φ))
              (Jt := Fin (Nat.card (FacetIndex (toDNF φ)))) (canonAm atoms (toDNF φ))
              (canonBv atoms (toDNF φ) (latticeScale (P.precision gammaHat)))
              cen gammaHat (canonDm M (toDNF φ) (P.precision gammaHat)))
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) s) :
    (1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime (canonRfac (toDNF φ))
              (Jt := Fin (Nat.card (FacetIndex (toDNF φ)))) (canonAm atoms (toDNF φ))
              (canonBv atoms (toDNF φ) (latticeScale (P.precision gammaHat)))
              cen gammaHat (canonDm M (toDNF φ) (P.precision gammaHat)))
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
  refine ttc_volume_endToEnd atoms φ ε δ hε0 hε1 hδ0 hδ1 hn _ rfl toDNF isDNF isPositive
    hm hr P hP hlen hbdd hcoeff cen gammaHat hgammaHat ball_subset
    (Fin (Nat.card (FacetIndex (toDNF φ)))) (canonAm atoms (toDNF φ))
    (canonBv atoms (toDNF φ) (latticeScale (P.precision gammaHat)))
    (fun i => canon_smul_region_subset_body atoms isPositive
      (latticeScale_pos (P.precision gammaHat)) i)
    (canonRfac (toDNF φ)) (by rw [canonRfac]; exact_mod_cast hr) ?_
    (canonDm (fun a => (atoms a).halfspace) (toDNF φ) (P.precision gammaHat))
    (canon_dist_le_canonDm atoms isPositive isDNF hbdd (P.precision gammaHat)) big
  rw [canonRfac, Fintype.card_fin]

/-! ## 7. The sampling law at the canonical description -/

/-- **The end-to-end sampling law at the canonical description.**  Definitionally the
`Ttc.e2eSampD …` that `Ttc.ttc_volume_endToEnd_canon` already contains; it is given a
name only so the non-vacuity statements below can mention the law without repeating
the whole description.

It **asserts nothing**: it is a `def` whose body *is* the term appearing in the
capstone, and `Ttc.Box.bxCanonSampD_eq` re-checks that identification by `rfl` at the
witness rather than leaving it to the name.

**Cost.**  Unfolding this name costs nothing, but the object it names is expensive:
the row index is `Fin (Nat.card (FacetIndex D))`, the facet count of the **whole**
DNF, so each cube's system carries one row per literal of every cube.  `Ttc.toDNF`
can return exponentially many cubes, so that row count is exponential in the input
size in the worst case; and the ball walk whose law this is takes
`2^Θ(n)·log(M·Vol(P′)/ε′)` steps. -/
noncomputable def canonSampD (atoms : A → LinAtom n) (D : DNF A) (P : Params)
    (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ) : Cube A → Space n → ℝ :=
  e2eSampD (fun a => (atoms a).halfspace) D (P.precision gammaHat) P.epsPrime
    (canonRfac D) (Jt := Fin (Nat.card (FacetIndex D))) (canonAm atoms D)
    (canonBv atoms D (latticeScale (P.precision gammaHat))) cen gammaHat
    (canonDm (fun a => (atoms a).halfspace) D (P.precision gammaHat))

/-! ## 8. Non-vacuity: the box, with the canonical description

`Ttc.Box.ttc_volume_endToEnd_box_at` (`Exec/EndToEnd`) instantiates
`Ttc.ttc_volume_endToEnd` on the box `[0,c]ⁿ` using the box's *hand-written* linear
description (`Ttc.Box.bxNormal`, `Ttc.Box.bxOffsetOf`, `Ttc.Box.bfac`,
`Ttc.Box.bxDm`).  What follows does the same for `Ttc.ttc_volume_endToEnd_canon`,
where there is nothing to hand-write: the description is
`Ttc.canonAm`/`Ttc.canonBv`/`Ttc.canonDm` at the box's own atoms.

Without this section `Ttc.ttc_volume_endToEnd_canon` could be vacuously true — no
tuple of inputs satisfying its binders would have been exhibited.
-/

namespace Box

/-- **The box's ball-walk sampler's discrete law, at the *canonical* description.**
`Ttc.Box.bxSampD` with `Ttc.Box.bxNormal`/`Ttc.Box.bxOffsetOf`/`Ttc.Box.bfac`/
`Ttc.Box.bxDm` replaced by the description `Ttc.ttc_volume_endToEnd_canon`
constructs. -/
noncomputable def bxCanonSampD (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) : Cube (Fin n ⊕ Fin n) → Space n → ℝ :=
  e2eSampD (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
    (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
    (parS n hn ε δ hε0 hε1).epsPrime
    (canonRfac (Ttc.toDNF (boxForm n hn)))
    (Jt := Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
    (canonAm (boxAtoms n (sideS n hn ε δ hε0 hε1)) (Ttc.toDNF (boxForm n hn)))
    (canonBv (boxAtoms n (sideS n hn ε δ hε0 hε1)) (Ttc.toDNF (boxForm n hn))
      (latticeScale (rhoS n hn ε δ hε0 hε1)))
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1)
    (canonDm (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1))

variable (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)

/-- **The box's ball-walk sampler at the canonical description**, with no accuracy
assumption: every input of `Ttc.e2eSampler` is discharged by §1–§4 of this file, and
its one quantitative field `law_tv` is a theorem
(`Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`), not a hypothesis.

**Cost.**  The certified step count behind `law_tv` is `2^Θ(n)·log(M·Vol(P′)/ε′)`;
this exhibits a sampler, it does not exhibit a fast one. -/
noncomputable def bxCanonSampler :
    KV97Sampler (Fin n ⊕ Fin n) n
      (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
      (parS n hn ε δ hε0 hε1).epsPrime (bxCanonSampD n hn ε δ hε0 hε1) :=
  e2eSampler hn (parS_epsPrime_pos (δ := δ) hn hε0 hε1)
    (Fin (Nat.card (FacetIndex (Ttc.toDNF (boxForm n hn)))))
    (canonAm (boxAtoms n (sideS n hn ε δ hε0 hε1)) (Ttc.toDNF (boxForm n hn)))
    (canonBv (boxAtoms n (sideS n hn ε δ hε0 hε1)) (Ttc.toDNF (boxForm n hn))
      (latticeScale (rhoS n hn ε δ hε0 hε1)))
    (fun i => canon_smul_region_subset_body (boxAtoms n (sideS n hn ε δ hε0 hε1))
      (toDNF_isPositive (boxForm_isPositive hn))
      (latticeScale_pos (rhoS n hn ε δ hε0 hε1)) i)
    (canonRfac (Ttc.toDNF (boxForm n hn)))
    (by rw [canonRfac]; exact_mod_cast one_le_card_facets_box n hn)
    (by rw [canonRfac, Fintype.card_fin])
    (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) (gamS_pos hn hε0 hε1)
    (ball_subset_bxOf n (sideS n hn ε δ hε0 hε1) hn)
    (canonDm (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
      (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1))
    (canon_dist_le_canonDm (boxAtoms n (sideS n hn ε δ hε0 hε1))
      (toDNF_isPositive (boxForm_isPositive hn)) (toDNF_isDNFOf (boxForm n hn))
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

/-- **`Ttc.ttc_volume_endToEnd_canon`'s `big`, for the box**, at every coin on which
the volume oracle got the volume right.  The route to the rates is
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

/-- **`Ttc.ttc_volume_endToEnd_canon`'s hypotheses are satisfiable, at every
`(ε, δ) ∈ (0,1]²`.**

The box `[0,c]ⁿ` with `c = max 1 Thresh(ε, δ)`, carrying **no oracle and no supplied
linear description**: the volume estimates are the Monte-Carlo oracle's own output,
the rates are `Ttc.rates` built on them, the sampler is the lazy ball walk of
`Ttc.kv97SamplerOfBody`, and the polytope description is
`Ttc.canonAm`/`Ttc.canonBv`/`Ttc.canonDm` — read off the box's atoms.  The only
inputs are the box's geometry.

**Costs and scope, quoted here rather than only upstream.**  The guarantee is
`1 − δ − δ/4` (the extra `δ/4` is the Monte-Carlo volume oracle's failure
probability) and the run-cost conjunct is `alg:ttc`'s charged
`m·(C_vol + C_sample·Thresh)`, with `m = 1` here: `Ttc.Box.length_toDNF_boxForm`
makes this a **single-cube** DNF, so `hlen`, the `m`-way union bound and the per-cube
error composition are not exercised beyond arity one.  Both constructions are
exponential in `n` — hit-and-miss Monte Carlo at `Θ(Rⁿ/(ε²p))` samples, ball walk at
`2^Θ(n)·log(M·Vol(P′)/ε′)` steps — so this is a satisfiability witness, not an
efficiency claim. -/
theorem ttc_volume_endToEnd_canon_box_at (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
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
  ttc_volume_endToEnd_canon (boxAtoms n (sideS n hn ε δ hε0 hε1)) (boxForm n hn) ε δ
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

/-- The box's canonical law is `Ttc.canonSampD` at the box's data — checked by `rfl`,
so the name `Ttc.canonSampD` is not standing in for an unproved identification. -/
theorem bxCanonSampD_eq :
    bxCanonSampD n hn ε δ hε0 hε1
      = canonSampD (boxAtoms n (sideS n hn ε δ hε0 hε1)) (Ttc.toDNF (boxForm n hn))
          (parS n hn ε δ hε0 hε1) (cenMC n hn ε δ hε0 hε1) (gamS n hn ε δ hε0 hε1) := rfl

/-! ### The pair, and the guarantee is a strictly positive real number

One witness cannot distinguish "the hypotheses are satisfiable" from "the hypotheses
force one accuracy pair", so `Ttc.Box.AtParamsCanon` packages the conclusion of
`Ttc.ttc_volume_endToEnd_canon` over the data it is stated about, with `(ε, δ)`
exposed, and `Ttc.Box.exists_two_ttc_volume_endToEnd_canon_instances` produces **two**
inhabitants at two different pairs.

`AtParamsCanon` asserts nothing that is not proved: `Ttc.Box.atParamsCanon_of`
establishes it at every `(ε, δ)` with `0 < ε ≤ 1`, `0 < δ ≤ 1` and a **positive
accuracy budget** `0 < 1 − δ − δ/4` (i.e. `δ < 4/5`).  The budget hypothesis is what
buys the strict positivity conjunct below; above `δ = 4/5` the budget is not positive
and `1 − δ − δ/4 ≤ x` certifies nothing about a `toReal`, so that corner is not
claimed. -/

/-- **`Ttc.ttc_volume_endToEnd_canon`'s conclusion, with `(ε, δ)` exposed.**

Unlike `Ttc.Box.AtParamsE2E`, the sampling law is not existentially quantified: it is
`Ttc.canonSampD`, the law forced by the **canonical** linear description of the input
polytopes.  Six of the theorem's hypotheses travel with it — the parameter block
really is at the stated accuracy, the DNF is positive, the solution set is bounded,
`γ̂ > 0`, the **sampler exists** at these parameters, and the rates are **strictly
positive** at every coin the volume oracle got right — so a degenerate instance (an
uninhabited `Ttc.KV97Sampler`, or the collapsed `θ ≡ 0` that satisfies `theta_eq`
vacuously) cannot satisfy it.

The accuracy conjunct is deliberately stronger than the capstone's own: it names the
achieved probability `I`, and asserts not only `1 − δ − δ/4 ≤ I.toReal` but also
`0 < I.toReal` and `I ≠ ⊤`.  Without the last two the conjunct would be satisfiable
by `I = ⊤` (whose `toReal` is `0`) whenever the budget is non-positive, which is the
`toReal` vacuity trap. -/
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
    (∃ I : ENNReal,
      I = (∫⁻ c, trajLaw (rates (fun a => (atoms a).halfspace) φ (Ttc.toDNF φ)
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
        ∂(MonteCarlo.coins n)) ∧
      1 - δ - δ / 4 ≤ I.toReal ∧ 0 < I.toReal ∧ I ≠ ⊤)
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

/-- **The description-free capstone is instantiable at every accuracy pair with a
positive budget.**  The witness is the box, its Monte-Carlo volume oracle, its
constructed rates, and the lazy ball walk run on the **canonical** polytope
description.

`hbudget : 0 < 1 − δ − δ/4` is what makes the achieved probability provably strictly
positive and finite; it holds exactly when `δ < 4/5`.  Costs are as in
`Ttc.Box.ttc_volume_endToEnd_canon_box_at`: a single-cube DNF, and both the volume
oracle and the sampler exponential in `n`. -/
theorem atParamsCanon_of (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hbudget : 0 < 1 - δ - δ / 4) : AtParamsCanon n ε δ := by
  obtain ⟨hacc, hrun⟩ := ttc_volume_endToEnd_canon_box_at n hn ε δ hε0 hε1 hδ0 hδ1
  have hpos : 0 < (∫⁻ c, trajLaw
        (rates (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
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
      ∂(MonteCarlo.coins n)).toReal := lt_of_lt_of_le hbudget hacc
  exact ⟨boxAtoms n (sideS n hn ε δ hε0 hε1), boxForm n hn, parS n hn ε δ hε0 hε1,
    gamS n hn ε δ hε0 hε1, cenMC n hn ε δ hε0 hε1,
    hε0, hε1, hδ0, hδ1, rfl, rfl, rfl, gamS_pos hn hε0 hε1,
    toDNF_isPositive (boxForm_isPositive hn),
    isBounded_sol_bxOf n (sideS n hn ε δ hε0 hε1) hn,
    ⟨bxCanonSampler n hn ε δ hε0 hε1⟩,
    fun c hc s => bxCanonRates_pos n hn ε δ hε0 hε1 c hc s,
    ⟨_, rfl, hacc, hpos, (ENNReal.toReal_pos_iff.1 hpos).2.ne⟩, hrun⟩

/-- **The guarantee is a genuine number, not `ENNReal.toReal ⊤ = 0`.**  Wherever the
budget `1 − δ − δ/4` is positive, the bound itself forces the integral to be finite
and nonzero.  Nothing is assumed here — it is read off the theorem. -/
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
  have hacc := (ttc_volume_endToEnd_canon_box_at n hn ε δ hε0 hε1 hδ0 hδ1).1
  rw [← hI] at hacc
  have hpos : 0 < I.toReal := lt_of_lt_of_le hbudget hacc
  exact ⟨(ENNReal.toReal_pos_iff.1 hpos).1, (ENNReal.toReal_pos_iff.1 hpos).2.ne⟩

/-- **`ε` and `δ` are not forced, and both instances are informative.**

`Ttc.Box.ttc_volume_endToEnd_canon_box_at` at two *different* accuracy pairs, both
strictly inside `(0,1)`, with the achieved guarantee written as a numeral and proved
strictly positive: `3/8` at `(1/2, 1/2)` and `11/16` at `(1/4, 1/4)`.  The two
instances are genuinely distinct data, not one instance twice: the accuracy pairs
differ in **both** coordinates (`ε₁ ≠ ε₂` and `δ₁ ≠ δ₂`), and through
`Ttc.Box.sideS` — the box's side length is `max 1 Thresh(ε, δ)` — the parameter block,
the side length, the lattice precision and the sampler all differ with them.

Strict positivity is asserted **inside** the statement, twice over: each
`Ttc.Box.AtParamsCanon` carries `0 < I.toReal` and `I ≠ ⊤` for its own achieved
probability `I`, and the numerals `3/8`, `11/16` that the budget evaluates to are
themselves proved positive.  (Above `δ = 4/5` the budget `1 − δ − δ/4` is not
positive; that corner certifies nothing and is not claimed.)

**Costs.**  Both instances are the single-cube box witness of
`Ttc.Box.ttc_volume_endToEnd_canon_box_at`: guarantee `1 − δ − δ/4`, charged run cost
`m·(C_vol + C_sample·Thresh)` at `m = 1`, hit-and-miss Monte Carlo at `Θ(Rⁿ/(ε²p))`
samples and a ball walk at `2^Θ(n)·log(M·Vol(P′)/ε′)` steps. -/
theorem exists_two_ttc_volume_endToEnd_canon_instances (n : ℕ) (hn : 1 ≤ n) :
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
      (by norm_num) (by norm_num),
    atParamsCanon_of n hn (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),
    by norm_num, by norm_num, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Box

end Ttc

/-! ## Axiom audit -/

#print axioms Ttc.canonAm
#print axioms Ttc.canonBv
#print axioms Ttc.canonRfac
#print axioms Ttc.canonDm
#print axioms Ttc.mem_canon_body_iff
#print axioms Ttc.mem_halfspace_iff_inner
#print axioms Ttc.lit_holds_iff_inner
#print axioms Ttc.mem_region_halfspace_iff
#print axioms Ttc.mem_smul_region_iff
#print axioms Ttc.canon_body_eq_smul_region
#print axioms Ttc.canon_body_one_eq_region
#print axioms Ttc.canon_smul_region_subset_body
#print axioms Ttc.isBounded_smul_region
#print axioms Ttc.canon_dist_le_canonDm
#print axioms Ttc.smul_body
#print axioms Ttc.body_comp_equiv
#print axioms Ttc.ttc_volume_endToEnd_canon
#print axioms Ttc.canonSampD

-- non-vacuity on the box
#print axioms Ttc.Box.bxCanonSampD
#print axioms Ttc.Box.bxCanonSampler
#print axioms Ttc.Box.bxCanonSampD_almostUniform
#print axioms Ttc.Box.sum_rates_ge_of_almostUniform
#print axioms Ttc.Box.big_canon_box
#print axioms Ttc.Box.bxCanonRates_pos
#print axioms Ttc.Box.ttc_volume_endToEnd_canon_box_at
#print axioms Ttc.Box.bxCanonSampD_eq
#print axioms Ttc.Box.AtParamsCanon
#print axioms Ttc.Box.atParamsCanon_of
#print axioms Ttc.Box.canon_box_lintegral_pos_ne_top
#print axioms Ttc.Box.exists_two_ttc_volume_endToEnd_canon_instances

-- The headline's binder list, echoed so a reader can check it is what §6 states and
-- that nothing in §7–§8 changed it: 26 explicit binders plus the two implicit
-- `{A : Type*} {n : ℕ}`.
#check @Ttc.ttc_volume_endToEnd_canon
