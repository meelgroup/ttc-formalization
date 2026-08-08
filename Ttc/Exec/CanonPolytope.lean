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

## Costs

No cost model changes: this file only substitutes values for binders of
`Ttc.ttc_volume_endToEnd`, whose cost conclusion
`runCost … ≤ (toDNF φ).length * (cVol + cSample * thresh)` — `alg:ttc`'s `m·(C_vol +
C_sample·Thresh)` — is reproduced verbatim in `Ttc.ttc_volume_endToEnd_canon`.  The
facet count `r` that `Ttc.Params.gamma` and `Ttc.Params.thresh` read is the same
`Nat.card (FacetIndex (toDNF φ))` the parameter block `Ttc.ttcParams` already stores,
so `rfac := Ttc.canonRfac (toDNF φ)` introduces no slack: `hcard` holds with equality.

## What is *not* claimed

Nothing here says the presentation is irredundant, or that the polytope is bounded
beyond what `hbdd` gives; and, as in `Ttc.ttc_volume_endToEnd`, the sampler is a
finite-time lazy ball-walk iterate meeting `Ttc.KV97Sampler.law_tv`, not a claim of
exact stationarity.
-/

namespace Ttc

open MeasureTheory Set Pointwise
open scoped InnerProductSpace

variable {A : Type*} {n : ℕ}

/-! ## 1. The canonical linear system -/

section System

/-- **The facets of `D`, enumerated.**  `Ttc.instFiniteFacetIndex` makes
`FacetIndex D` finite, so it is in bijection with `Fin (Nat.card (FacetIndex D))`.
The enumeration is needed only because the sampler's row index `Jt` lives in
`Type 0` while `FacetIndex D` lives in `A`'s universe; nothing below depends on
*which* bijection is chosen, only that it is one. -/
noncomputable def facetOf (D : DNF A) : Fin (Nat.card (FacetIndex D)) ≃ FacetIndex D :=
  (Finite.equivFin (FacetIndex D)).symm

open scoped Classical in
/-- **The canonical normal vectors.**  Row `k` of cube `i`'s system is the coefficient
vector of the atom under row `k`'s literal when that facet belongs to `i`, and the
zero vector otherwise. -/
noncomputable def canonAm (atoms : A → LinAtom n) (D : DNF A) (i : {c : Cube A // c ∈ D})
    (k : Fin (Nat.card (FacetIndex D))) : Space n :=
  if (facetOf D k).1 = i then WithLp.toLp 2 (atoms (facetOf D k).2.val.atom).coeff else 0

open scoped Classical in
/-- **The canonical offsets**, dilated by `s`: the atom's bound scaled by `s` on the
rows belonging to cube `i`, and `0` elsewhere. -/
noncomputable def canonBv (atoms : A → LinAtom n) (D : DNF A) (s : ℝ)
    (i : {c : Cube A // c ∈ D}) (k : Fin (Nat.card (FacetIndex D))) : ℝ :=
  if (facetOf D k).1 = i then s * (atoms (facetOf D k).2.val.atom).bound else 0

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

/-- `hdil` itself, as `Ttc.ttc_volume_endToEnd` asks for it. -/
theorem canon_smul_region_subset_body (atoms : A → LinAtom n) {D : DNF A}
    (hpos : DNF.IsPositive D) {s : ℝ} (hs : 0 < s) (i : {c : Cube A // c ∈ D}) :
    s • region (fun a => (atoms a).halfspace) i.val
      ⊆ Arlib.Polytope.body (canonAm atoms D i) (canonBv atoms D s i) :=
  (canon_body_eq_smul_region atoms hpos hs i).ge

/-! ## 4. The facet bound and the diameter -/

/-- **The canonical facet bound**: the exact facet count, so `hcard` holds with
equality and no slack enters `Ttc.Params.gamma` or `Ttc.Params.thresh`. -/
noncomputable def canonRfac (D : DNF A) : ℝ := (Nat.card (FacetIndex D) : ℝ)

/-- **The canonical diameter bound**: the metric diameter of the dilated region
itself.  Finite because `Bornology.IsBounded (sol M φ)` — already a binder of
`Ttc.ttc_volume_endToEnd` — bounds every region. -/
noncomputable def canonDm (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) : ℝ :=
  Metric.diam (latticeScale ρ • region M i.val)

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
    (isBounded_region_of_isBounded_sol hD hbdd i.property).smul₀ _
  intro x hx y hy
  rw [heq] at hx hy
  exact Metric.dist_le_diam_of_mem hb hx hy

/-! ## 5. The capstone, with the ten binders gone -/

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

end Ttc

/-! ## Axiom audit -/

#print axioms Ttc.canonAm
#print axioms Ttc.canonBv
#print axioms Ttc.canonRfac
#print axioms Ttc.canonDm
#print axioms Ttc.mem_canon_body_iff
#print axioms Ttc.mem_region_halfspace_iff
#print axioms Ttc.mem_smul_region_iff
#print axioms Ttc.canon_body_eq_smul_region
#print axioms Ttc.canon_smul_region_subset_body
#print axioms Ttc.canon_dist_le_canonDm
#print axioms Ttc.ttc_volume_endToEnd_canon
