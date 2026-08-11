/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude

/-!
# The canonical linear description of the dilated cubes

Plain convex geometry read off the formula: the `(Am, bv)` system a cube's region is cut
out by, the facet count, and the diameter.  No randomness anywhere in it, and no choice
beyond the enumeration of the facet index.

## Why this is not in `Model/Prelude`

It used to be, on the grounds that it is the geometry the sampler is *applied at* and is
built from `Ttc.region`, `Ttc.latticeScale` and `Ttc.FacetIndex`, which are vocabulary.
That grouping was topical rather than structural, and it made `Model/` carry five
definitions that say nothing about the problem statement — a reader checking *what is
being claimed* never needs them, while a reader checking *what the algorithm does* reaches
them through `Ttc.ttc` regardless of which file they sit in.

The move has one consequence a reader must be told about rather than left to discover:
`Ttc.Audit.auditSurface` now names three directories, not two.  These five constants are in
the definitional closure of `Ttc.ttc`, so `#modelClosure Ttc.ttc` would fail outright if
`Ttc.Geometry` were not admitted.  The promise the check enforces is correspondingly
"`Model/`, `Probability/` and `Geometry/`" — and `Ttc/Audit/ClosureCheck.lean` states the
bound on what may go here: **definitions only, no `Prop`s, and nothing that is not convex
geometry determined by the formula**.  Every *property* of these objects continues to be
proved outside the surface.

The statement of `Ttc.ttc_volume_estimate` does not mention any of them, so
`#modelClosureOfType` on the headline is unaffected.
-/

namespace Ttc

open scoped Pointwise

/-- **The facets of `D`, enumerated.**  `Ttc.instFiniteFacetIndex` makes `FacetIndex D`
finite, so it is in bijection with `Fin (Nat.card (FacetIndex D))`.  The enumeration is
needed only because the sampler's row index lives in `Type 0` while `FacetIndex D` lives
in `A`'s universe; nothing depends on *which* bijection is chosen. -/
noncomputable def facetOf {A : Type*} (D : DNF A) :
    Fin (Nat.card (FacetIndex D)) ≃ FacetIndex D :=
  (Finite.equivFin (FacetIndex D)).symm

open scoped Classical in
/-- **The canonical normal vectors.**  Row `k` of cube `i`'s system is the coefficient
vector of the atom under row `k`'s literal when that facet belongs to `i`, and the
zero vector otherwise. -/
noncomputable def canonAm {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (D : DNF A)
    (i : {c : Cube A // c ∈ D}) (k : Fin (Nat.card (FacetIndex D))) : Space n :=
  if (facetOf D k).1 = i then WithLp.toLp 2 (atoms (facetOf D k).2.val.atom).coeff else 0

open scoped Classical in
/-- **The canonical offsets**, dilated by `s`: the atom's bound scaled by `s` on the
rows belonging to cube `i`, and `0` elsewhere. -/
noncomputable def canonBv {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (D : DNF A) (s : ℝ)
    (i : {c : Cube A // c ∈ D}) (k : Fin (Nat.card (FacetIndex D))) : ℝ :=
  if (facetOf D k).1 = i then s * (atoms (facetOf D k).2.val.atom).bound else 0

/-- **The canonical facet bound**: the exact facet count, so `hcard` holds with
equality and no slack enters `Ttc.Params.gamma` or `Ttc.Params.thresh`. -/
noncomputable def canonRfac {A : Type*} (D : DNF A) : ℝ := (Nat.card (FacetIndex D) : ℝ)

/-- **The canonical diameter bound**: the metric diameter of the dilated region
itself. -/
noncomputable def canonDm {A : Type*} {n : ℕ} (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) : ℝ :=
  Metric.diam (latticeScale ρ • region M i.val)

end Ttc
