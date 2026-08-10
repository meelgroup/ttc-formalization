/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude
import Ttc.Probability.BallWalk
import Arlib.Lattice.KV97.InflateGeom
import Arlib.Lattice.Rounding.ProdKernel

/-!
# `GenerateSamples`' two laws: the continuous draw and the rounded, rejected draw

The lazy ball walk on the Kannan–Vempala inflated polytope, and the randomized-rounding
rejection law its discrete output has.

**Vocabulary only.**  Three definitions, no `Prop`, nothing assumed.  All three are
*laws*: `Ttc.kv97ContLaw` is a measure, `Ttc.kv97SampD` and `Ttc.e2eSampD` are the mass
function the rounding-then-rejection produces.  Nothing about the target measure appears
in any of them — only `Ttc.tvLe_ballWalkLaw_inflated` and the rejection lemmas
(`Sampler/Construct`, `Sampler/Contract`) tie them to the uniform distribution, and those
are downstream.

**This is the one file of `Ttc/Probability/` that is not Mathlib-and-`Arlib`-only.**  It
imports `Ttc.Model.Prelude`, because the mass function is indexed by the cubes of a DNF
and normalised over a cube's own region: `Ttc.Cube`, `Ttc.DNF`, `Ttc.region`,
`Ttc.latticeScale` and `Ttc.intLattice` are all genuinely in its *statement*, not merely
in its proofs.  Making it independent of `Model/Prelude` would mean re-indexing it over an
abstract index type and an abstract region map, i.e. changing its signature and every one
of its call sites; that is a different piece of work and is not done here.

The **geometry** the sampler is applied at — `Ttc.facetOf`, `Ttc.canonAm`, `Ttc.canonBv`,
`Ttc.canonDm`, `Ttc.canonRfac` — is *not* probability and stays in `Model/Prelude` with
the rest of the convex-geometry vocabulary.

This file used to be part of `Model/Prelude`; see `Ttc/Audit/ClosureCheck.lean` for why
the audit surface is `Ttc/Model/` **together with** `Ttc/Probability/`.
-/

namespace Ttc

open MeasureTheory
open scoped Pointwise

open scoped Classical in
/-- **The sampler's discrete law**: the mass at a fine-lattice point `x` of `P(c)` is the
probability that randomized rounding of the continuous draw `law ⟨c,·⟩` lands on
`10^ρ · x`, normalised by the same quantity summed over all integer points of the dilated
polytope.  Outside the cubes of `D` there is nothing to define and the value is `0`. -/
noncomputable def kv97SampD {A : Type*} {n : ℕ} (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (law : {c : Cube A // c ∈ D} → Measure (Space n)) : Cube A → Space n → ℝ := fun c x =>
  if hc : c ∈ D then
    (∫ p, Arlib.Lattice.Rounding.prodTent (latticeScale ρ • x) p ∂(law ⟨c, hc⟩)) /
      ∑ᶠ k : ((latticeScale ρ • region M c) ∩ intLattice n : Set (Space n)),
        ∫ p, Arlib.Lattice.Rounding.prodTent (k : Space n) p ∂(law ⟨c, hc⟩)
  else 0

/-- **The sampler's continuous law**: for each cube `i`, the law of the lazy ball walk on
the inflated dilated polytope `P'ᵢ`, run from the warm start `mu0 i` for `Ttc.mixSteps`
steps at tolerance `ε'/(4·Vol(P'ᵢ))`. -/
noncomputable def kv97ContLaw {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime r : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (Dm γ δ Mw : {c : Cube A // c ∈ D} → ℝ)
    (mu0 : {c : Cube A // c ∈ D} → Measure (Space n)) :
    {c : Cube A // c ∈ D} → Measure (Space n) := fun i =>
  ballWalkLaw (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r) (δ i) (mu0 i)
    (mixSteps n (γ i) (Dm i) (δ i) (Mw i)
      (epsPrime / (4 *
        (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r)).toReal)))

/-- **The sampler's discrete law, at the geometry the run already carries** — the
rounding-then-rejection law of the lazy ball walk on the inflated dilated body, with its
inscribed ball the run's own dilated ball and its ball-walk step equal to that radius. -/
noncomputable def e2eSampD {A : Type*} {n : ℕ} (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (epsPrime rfac : ℝ) {Jt : Type}
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ)
    (Dm : {c : Cube A // c ∈ D} → ℝ) : Cube A → Space n → ℝ :=
  kv97SampD M D ρ (kv97ContLaw epsPrime rfac Am bv
    (fun i => (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac /
        (latticeScale ρ * gammaHat)) * Dm i)
    (fun _ => latticeScale ρ * gammaHat
      + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
    (fun _ => latticeScale ρ * gammaHat)
    (fun i => (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac) /
      volume (Metric.ball (latticeScale ρ • cen i)
        (latticeScale ρ * gammaHat
          + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))).toReal)
    (fun i => Arlib.uniformOn volume (Metric.ball (latticeScale ρ • cen i)
      (latticeScale ρ * gammaHat
        + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))))

end Ttc
