/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.ProblemSetting
import Arlib.MarkovChains.Continuous.ConvexBodyMixing
import Arlib.MarkovChains.Continuous.WarmStart
import Arlib.MarkovChains.Continuous.WarmStartGeneral
import Arlib.Lattice.KV97.InflateGeom
import Arlib.Lattice.Rounding.ProdKernel

/-!
# `Sampler/Construct`: a `Ttc.KV97Sampler` whose `law_tv` is a theorem

`Ttc.KV97Sampler` (`Ttc/Model/ProblemSetting.lean`) has fifteen fields.  Fourteen
are *descriptive* — they say which polytope the sampler runs on, how it is
normalised, and what its output law is.  Exactly one is *quantitative*:

    law_tv : ∀ i, Arlib.TVLe (contLaw i)
      (Arlib.uniformOn volume (Arlib.KV97.inflated (Amat i) (bvec i) (cOf ε') r))
      (ENNReal.ofReal (ε' / (4 * contVol i)))

Up to now `law_tv` was *assumed*: the development quantified over a
`KV97Sampler` and never built one whose `contLaw` was an actual algorithm.  This
file builds one.

## What `contLaw` is here

`contLaw i` is the law of the **lazy ball walk** on the inflated polytope
`P'ᵢ = Arlib.KV97.inflated (Amat i) (bvec i) (cOf ε') r`, started from a warm
start `mu0 i` and run for `mixSteps` steps:

    contLaw i = Arlib.MarkovChains.iterate
                  (lazy (ballWalk P'ᵢ (δ i))) (mu0 i) (mixSteps …)

(`Ttc.ballWalkLaw`, `Ttc.kv97ContLaw`).  It is a Markov-chain iterate, not the
target measure inserted by hand — see the *non-vacuity* section below, which is
the reason this distinction is spelled out rather than left to the reader.

`law_tv` is then `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope`
(`Arlib/MarkovChains/Continuous/ConvexBodyMixing.lean`) instantiated at
`eps := ε' / (4 · Vol(P'ᵢ))`.  That theorem is **unconditional** in the two places
this used to break: it assumes *no* isoperimetric inequality (supplied internally
by `Arlib.uniformOn_iso_of_convex`) and *no* local-conductance floor (supplied by
`Arlib.MarkovChains.le_ell_of_convex_of_ball_subset`).  Its target is exactly the
walk's own stationary measure (`isReversible_ballWalk`), so the conclusion carries
**no bias term**: the only error is `eps`, and `eps` is chosen to be the tolerance
`law_tv` wants.  Hence the step count

    mixSteps n γ D δ M eps = conductanceMixingTime M
      (min ((γ/(γ+D))ⁿ/32) ((1/2)ⁿ/D · ((γ/(γ+D))ⁿ)² · δ/(128 n))) eps

is *the whole content* of the quantitative field.

## What is still assumed, and why that is not a hole

`Ttc.kv97SamplerOfBallWalk` takes the geometry of the *inflated* body `P'ᵢ` — a
diameter bound and an inscribed ball — and a warm start `mu0 i`, as **explicit
named hypotheses**, not as fields of a new structure and not as axioms.

`Ttc.kv97SamplerOfBody` removes all of that.  Using
`Arlib.KV97.ball_subset_inflated` / `Arlib.KV97.dist_le_of_mem_inflated`
(`Arlib/Lattice/KV97/InflateGeom.lean`) and
`Arlib.MarkovChains.isWarm_uniformOn_inscribed`
(`Arlib/MarkovChains/Continuous/WarmStartGeneral.lean`), it asks only for

* an inscribed ball `B(cen i, γ i) ⊆ P(cᵢ)` of the **original** polytope, and
* a diameter bound `Dm i` for `P(cᵢ)`,

and constructs the inflated geometry and the warm start itself.  Those two
remaining inputs are genuine facts about the *problem instance* — an unbounded or
lower-dimensional `P(cᵢ)` has neither — and are exactly the binders the `Ttc`
capstone already carries (`ball_subset`, boundedness).  They are not statements
about the sampler.  `Ttc.exists_kv97Sampler_box` discharges every hypothesis for
a concrete body, so the bundle is demonstrably satisfiable.

## The step count is exponential in `n`

`min ((γ/(γ+D))ⁿ/32) (…)` is exponentially small in the dimension: the
isoperimetric constant behind it is `2⁻ⁿ/D` and the local-conductance floor is
`(γ/(γ+D))ⁿ`.  `conductanceMixingTime` is `O(φ⁻² log (M/eps))`, so `mixSteps`
is `2^{Θ(n)} · log(M · Vol(P')/ε')`.  **This is not a polynomial-time sampler and
must not be quoted as one.**  The `1/Vol(P')` inside `eps` is by contrast cheap:
it enters only through `log`, which is the point
`Arlib.PointwiseRoute.conductanceMixingTime_inv_volume_le` makes.

## Non-vacuity, and the trap this file had to avoid

The cheap way to "discharge" `law_tv` is to take `contLaw i` to *be*
`Arlib.uniformOn volume P'ᵢ`, whereupon `law_tv` follows from `TVLe.refl`.  That
would assume the very sampler being constructed — the disguised-oracle failure of
`CLAUDE.md` §11.  So the file carries, in the style of
`Arlib.MarkovChains.exists_unconditional_mixing_unitBall_nonstationary`:

* `Ttc.kv97ContLaw_eq_iterate` — `contLaw` really is a chain iterate;
* `Ttc.kv97SamplerOfBody_start_ne_target` — the start `Ttc.kv97SamplerOfBody`
  builds is not the target measure, given properness of the inscribed ball;
* `Ttc.exists_kv97Sampler_box` — a fully concrete instance (the box
  `{x | ∀ i, |xᵢ| ≤ 1}` and its Kannan–Vempala inflation) whose start is the
  uniform law on a strictly smaller ball, with `mu0 ≠ uniformOn volume P'` proved
  as a conjunct inside the existential, and with the tolerance proved
  `≤ 1/2` — hence not the vacuous `≥ 1` — so that `law_tv` really constrains the
  law.

**What is *not* proved** (stated here so no reader over-reads the file):
`contLaw i ≠ Arlib.uniformOn volume P'ᵢ`.  A finite-time iterate of an ergodic
chain from a non-stationary start is never exactly stationary, but proving it
needs the `L²` spectral input that the chain has no eigenvalue `−1` (aperiodicity
in the continuous setting), which is not available here.  What *is* proved is
strictly weaker and stated honestly: the start is not the target, the law is a
`mixSteps`-fold iterate of the walk kernel applied to that start, and the
tolerance the theorem meets is a non-trivial one.

## Main results

* `Ttc.mixSteps`, `Ttc.ballWalkLaw`, `Ttc.kv97ContLaw` — the construction.
* `Ttc.tvLe_ballWalkLaw_inflated` — the quantitative core: the `t`-step law is
  within `eps` of uniform on `P'`, unconditionally.
* `Ttc.kv97SampD` — the rejection-normalised rounding law, so `sampD_eq` is a
  definition rather than an assumption.
* `Ttc.kv97SamplerOfBallWalk` — **the `KV97Sampler` term**, with `law_tv` proved.
* `Ttc.kv97SamplerOfBody` — the same, with the inflated-body geometry and the warm
  start *derived* rather than assumed; only the original polytope's inscribed ball
  and diameter remain as inputs.
* `Ttc.kv97SamplerOfBody_start_ne_target` — its start is not the target measure.
* `Ttc.exists_kv97Sampler_box` — non-degenerate inhabitation.

## A note on the witness's inscribed ball

`Ttc.exists_kv97Sampler_box` deliberately uses `γ = 1` — the unit ball — rather
than the maximal inscribed ball of radius `1 + κ`.  With the maximal ball the
inclusion `B ⊆ P'` is not *proper in measure* at `n = 1` (the open interval
`(−(1+κ), 1+κ)` and the closed box `[−(1+κ), 1+κ]` have the same volume), the
start would coincide with the stationary measure, and the witness would collapse
into exactly the degeneracy this file is guarding against.  With `γ = 1` the
inflation `κ > 0` (`Ttc.kappaOf_cOf_pos`) makes the inclusion strict in every
dimension.
-/

namespace Ttc

open MeasureTheory Pointwise
open scoped ENNReal

/-! ## The chain and its step count -/

/-- **The step count.**  `Arlib.MarkovChains.conductanceMixingTime` at the conductance
floor that `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` produces for a body of
diameter `Dm` containing a ball of radius `γ`, walked with step `δ` from an `Mw`-warm
start, to reach total-variation accuracy `eps`.

Exponentially large in `n`; see the module docstring. -/
noncomputable def mixSteps (n : ℕ) (γ Dm δ Mw eps : ℝ) : ℕ :=
  Arlib.MarkovChains.conductanceMixingTime Mw
    (min ((γ / (γ + Dm)) ^ n / 32)
      ((1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * δ / (128 * (n : ℝ)))) eps

/-- **The law of the lazy ball walk on `K` with step `δ` after `t` steps from `mu0`.**

This is the sampler's output law.  It is an iterate of a Markov kernel — nothing about
the target `Arlib.uniformOn volume K` appears in it. -/
noncomputable def ballWalkLaw {n : ℕ} (K : Set (Space n)) (δ : ℝ) (mu0 : Measure (Space n))
    (t : ℕ) : Measure (Space n) :=
  Arlib.MarkovChains.iterate (Arlib.MarkovChains.lazy (Arlib.MarkovChains.ballWalk K δ)) mu0 t

/-- `ballWalkLaw` is what it says it is: the `t`-th iterate of the lazy ball-walk kernel.
Stated so that a reader can check the sampler is a chain and not the target. -/
theorem ballWalkLaw_eq_iterate {n : ℕ} (K : Set (Space n)) (δ : ℝ) (mu0 : Measure (Space n))
    (t : ℕ) : ballWalkLaw K δ mu0 t
      = Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy (Arlib.MarkovChains.ballWalk K δ)) mu0 t := rfl

/-- At `t = 0` the law is the start; the chain has done nothing yet. -/
@[simp] theorem ballWalkLaw_zero {n : ℕ} (K : Set (Space n)) (δ : ℝ) (mu0 : Measure (Space n)) :
    ballWalkLaw K δ mu0 0 = mu0 := rfl

/-- The output law is a probability measure. -/
instance isProbabilityMeasure_ballWalkLaw {n : ℕ} (K : Set (Space n)) (δ : ℝ)
    (mu0 : Measure (Space n)) [IsProbabilityMeasure mu0] (t : ℕ) :
    IsProbabilityMeasure (ballWalkLaw K δ mu0 t) :=
  Arlib.MarkovChains.isProbabilityMeasure_iterate _ _ t

/-! ## The quantitative core -/

/-- **The `mixSteps`-step law of the lazy ball walk on the Kannan–Vempala inflated
polytope is within `eps` of uniform on it, in total variation.**

This is `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` restated for
`Arlib.KV97.inflated` (which is `Arlib.Polytope.inflate` at `κ = Arlib.KV97.kappaOf cc r`)
and with the step count spelled as `Ttc.mixSteps`.  **No isoperimetric inequality and no
local-conductance hypothesis is assumed**, and the target is the walk's own stationary
measure, so there is no bias term: the only error is `eps`.

This is the whole content of `Ttc.KV97Sampler.law_tv`. -/
theorem tvLe_ballWalkLaw_inflated {n : ℕ} {ι : Type*} (hn : 1 ≤ n)
    (Am : ι → Space n) (bv : ι → ℝ) (cc r : ℝ) {Dm : ℝ}
    (hD : ∀ x ∈ Arlib.KV97.inflated Am bv cc r, ∀ y ∈ Arlib.KV97.inflated Am bv cc r,
      dist x y ≤ Dm)
    {cen : Space n} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ Arlib.KV97.inflated Am bv cc r)
    {δ : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ)
    {mu0 : Measure (Space n)} [IsProbabilityMeasure mu0] {Mw : ℝ} (hMw : 1 ≤ Mw)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal Mw) mu0
      (Arlib.uniformOn volume (Arlib.KV97.inflated Am bv cc r)))
    {eps : ℝ} (heps : 0 < eps) :
    Arlib.TVLe
      (ballWalkLaw (Arlib.KV97.inflated Am bv cc r) δ mu0 (mixSteps n γ Dm δ Mw eps))
      (Arlib.uniformOn volume (Arlib.KV97.inflated Am bv cc r)) (ENNReal.ofReal eps) := by
  exact Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope hn Am bv
    (Arlib.KV97.kappaOf cc r) hD hγ hball hδ hδγ hMw hwarm heps le_rfl

/-! ## Guards on the volume of `P'` -/

/-- `Vol(P') ≠ 0`, from the inscribed ball. -/
theorem volume_inflated_ne_zero {n : ℕ} {ι : Type*} {Am : ι → Space n} {bv : ι → ℝ} {cc r : ℝ}
    {cen : Space n} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ Arlib.KV97.inflated Am bv cc r) :
    volume (Arlib.KV97.inflated Am bv cc r) ≠ 0 :=
  Arlib.MarkovChains.volume_ne_zero_of_ball_subset hγ hball

/-- `Vol(P') ≠ ⊤`, from the diameter bound.  Needed because `ENNReal.toReal ⊤ = 0` would
otherwise make `contVol` vanish. -/
theorem volume_inflated_ne_top {n : ℕ} {ι : Type*} {Am : ι → Space n} {bv : ι → ℝ} {cc r : ℝ}
    {cen : Space n} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ Arlib.KV97.inflated Am bv cc r) {Dm : ℝ}
    (hD : ∀ x ∈ Arlib.KV97.inflated Am bv cc r, ∀ y ∈ Arlib.KV97.inflated Am bv cc r,
      dist x y ≤ Dm) : volume (Arlib.KV97.inflated Am bv cc r) ≠ ⊤ :=
  Arlib.MarkovChains.volume_ne_top_of_diam_bound (hball (Metric.mem_ball_self hγ)) hD

/-- `0 < Vol(P').toReal`, i.e. exactly the two side conditions `Vol(P') ∉ {0, ∞}` that
`Ttc.KV97Sampler.contVol_pos` is asked for. -/
theorem toReal_volume_inflated_pos {n : ℕ} {ι : Type*} {Am : ι → Space n} {bv : ι → ℝ}
    {cc r : ℝ} {cen : Space n} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ Arlib.KV97.inflated Am bv cc r) {Dm : ℝ}
    (hD : ∀ x ∈ Arlib.KV97.inflated Am bv cc r, ∀ y ∈ Arlib.KV97.inflated Am bv cc r,
      dist x y ≤ Dm) : 0 < (volume (Arlib.KV97.inflated Am bv cc r)).toReal :=
  ENNReal.toReal_pos (volume_inflated_ne_zero hγ hball) (volume_inflated_ne_top hγ hball hD)

/-! ## The rejection-normalised rounding law

`Ttc.KV97Sampler.sampD_eq` pins the discrete law to the rounding-then-rejection formula.
Defining `sampD` by that formula turns the field from an assumption into a `rfl`. -/

open scoped Classical in
/-- **The sampler's discrete law**, defined by the formula `sampD_eq` demands: the mass at
a fine-lattice point `x` of `P(c)` is the probability that randomized rounding of the
continuous draw `law ⟨c,·⟩` lands on `10^ρ · x`, normalised by the same quantity summed
over all integer points of the dilated polytope.

Outside the cubes of `D` there is nothing to define and the value is `0`; the structure
field constrains `sampD` only on `region M i.val ∩ fineLattice n (latticeScale ρ)` for
`i.val ∈ D`. -/
noncomputable def kv97SampD {A : Type*} {n : ℕ} (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (law : {c : Cube A // c ∈ D} → Measure (Space n)) : Cube A → Space n → ℝ := fun c x =>
  if hc : c ∈ D then
    (∫ p, Arlib.Lattice.Rounding.prodTent (latticeScale ρ • x) p ∂(law ⟨c, hc⟩)) /
      ∑ᶠ k : ((latticeScale ρ • region M c) ∩ intLattice n : Set (Space n)),
        ∫ p, Arlib.Lattice.Rounding.prodTent (k : Space n) p ∂(law ⟨c, hc⟩)
  else 0

/-- On a cube of `D`, `Ttc.kv97SampD` is exactly the right-hand side of
`Ttc.KV97Sampler.sampD_eq`. -/
theorem kv97SampD_apply {A : Type*} {n : ℕ} (M : A → Set (Space n)) {D : DNF A} (ρ : ℤ)
    (law : {c : Cube A // c ∈ D} → Measure (Space n)) (i : {c : Cube A // c ∈ D})
    (x : Space n) :
    kv97SampD M D ρ law i.val x =
      (∫ p, Arlib.Lattice.Rounding.prodTent (latticeScale ρ • x) p ∂(law i)) /
        ∑ᶠ k : ((latticeScale ρ • region M i.val) ∩ intLattice n : Set (Space n)),
          ∫ p, Arlib.Lattice.Rounding.prodTent (k : Space n) p ∂(law i) := by
  classical
  rw [kv97SampD, dif_pos i.2]

/-! ## The continuous law of the sampler -/

/-- **The `contLaw` field**: for each cube `i`, the law of the lazy ball walk on the
inflated dilated polytope `P'ᵢ`, run from the warm start `mu0 i` for `Ttc.mixSteps` steps at
tolerance `ε'/(4·Vol(P'ᵢ))`.

Note what is *absent* from the right-hand side: `Arlib.uniformOn`.  The law is produced by
iterating a kernel, and the only thing that ties it to the uniform measure is the mixing
theorem `Ttc.tvLe_ballWalkLaw_inflated`. -/
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

/-- **`contLaw` is a chain iterate, spelled out.**  This is the anti-trap lemma: it exhibits
the sampler's law as `iterate (lazy (ballWalk P'ᵢ δᵢ)) (mu0 i) t`, so that a reader can see
the target measure does not occur in the construction. -/
theorem kv97ContLaw_eq_iterate {A : Type*} {n : ℕ} {D : DNF A} {Jt : Type}
    (epsPrime r : ℝ)
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (Dm γ δ Mw : {c : Cube A // c ∈ D} → ℝ)
    (mu0 : {c : Cube A // c ∈ D} → Measure (Space n)) (i : {c : Cube A // c ∈ D}) :
    kv97ContLaw epsPrime r Am bv Dm γ δ Mw mu0 i
      = Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy (Arlib.MarkovChains.ballWalk
            (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r) (δ i)))
          (mu0 i)
          (mixSteps n (γ i) (Dm i) (δ i) (Mw i)
            (epsPrime / (4 *
              (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r)).toReal))) :=
  rfl

/-! ## The `KV97Sampler` term -/

/-- **A `Ttc.KV97Sampler` whose `law_tv` is a theorem.**

Fourteen fields are descriptive and are supplied by the caller's linear description of the
dilated polytopes (`Am`, `bv`, `hdil`, `r`, `hr1`, `hcard`) together with the construction
above (`contLaw = Ttc.kv97ContLaw`, `contVol = Vol(P')`, `sampD = Ttc.kv97SampD`).  The
fifteenth, `law_tv`, is `Ttc.tvLe_ballWalkLaw_inflated` — that is, the unconditional mixing
theorem `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` — instantiated at
`eps = ε'/(4·Vol(P'ᵢ))`.  **Nothing about the sampler's accuracy is assumed.**

The open hypotheses are geometric facts about the *inflated* polytope family and a warm
start for it:

* `hD` — a diameter bound `Dm i` for `P'ᵢ`;
* `hγ`, `hball` — an inscribed ball `B(cen i, γ i) ⊆ P'ᵢ`;
* `hδ`, `hδγ` — a ball-walk step `0 < δ i ≤ γ i`;
* `hmu0`, `hMw`, `hwarm` — an `Mw i`-warm start `mu0 i`.

None of these is an assumption *about the sampler*: they are properties of the body it runs
on, and `Arlib.MarkovChains.mixesWithin_lazy_ballWalk_polytope` carries exactly the same
ones.  `Ttc.exists_kv97Sampler_cube` discharges all of them for a concrete body.

The step count is exponential in `n`; see the module docstring. -/
noncomputable def kv97SamplerOfBallWalk
    {A : Type*} {n : ℕ} {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ} {epsPrime : ℝ}
    (hn : 1 ≤ n) (hEps : 0 < epsPrime)
    (Jt : Type) [Fintype Jt]
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (hdil : ∀ i, latticeScale ρ • region M i.val ⊆ Arlib.Polytope.body (Am i) (bv i))
    (r : ℝ) (hr1 : 1 ≤ r) (hcard : (Fintype.card Jt : ℝ) ≤ r)
    (Dm : {c : Cube A // c ∈ D} → ℝ)
    (hD : ∀ i, ∀ x ∈ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r,
      ∀ y ∈ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r, dist x y ≤ Dm i)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ : {c : Cube A // c ∈ D} → ℝ)
    (hγ : ∀ i, 0 < γ i)
    (hball : ∀ i, Metric.ball (cen i) (γ i) ⊆
      Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r)
    (δ : {c : Cube A // c ∈ D} → ℝ) (hδ : ∀ i, 0 < δ i) (hδγ : ∀ i, δ i ≤ γ i)
    (mu0 : {c : Cube A // c ∈ D} → Measure (Space n))
    (hmu0 : ∀ i, IsProbabilityMeasure (mu0 i))
    (Mw : {c : Cube A // c ∈ D} → ℝ) (hMw : ∀ i, 1 ≤ Mw i)
    (hwarm : ∀ i, Arlib.IsWarm (ENNReal.ofReal (Mw i)) (mu0 i)
      (Arlib.uniformOn volume
        (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r))) :
    KV97Sampler A n M D ρ epsPrime
      (kv97SampD M D ρ (kv97ContLaw epsPrime r Am bv Dm γ δ Mw mu0)) where
  J := Jt
  fintypeJ := inferInstance
  Amat := Am
  bvec := bv
  dilate_eq := hdil
  facetBound := r
  one_le_facetBound := hr1
  card_le_facetBound := hcard
  contLaw := kv97ContLaw epsPrime r Am bv Dm γ δ Mw mu0
  isProbContLaw := by
    intro i
    haveI := hmu0 i
    exact isProbabilityMeasure_ballWalkLaw _ _ _ _
  contVol := fun i =>
    (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r)).toReal
  contVol_pos := fun i => toReal_volume_inflated_pos (hγ i) (hball i) (hD i)
  contVol_eq := fun _ => rfl
  law_tv := by
    intro i
    haveI := hmu0 i
    have hpos : 0 < (volume
        (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r)).toReal :=
      toReal_volume_inflated_pos (hγ i) (hball i) (hD i)
    exact tvLe_ballWalkLaw_inflated hn (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r (hD i)
      (hγ i) (hball i) (hδ i) (hδγ i) (hMw i) (hwarm i)
      (div_pos hEps (by linarith))
  sampD_eq := fun i x _ => kv97SampD_apply M ρ _ i x

/-- **The same `KV97Sampler`, with every hypothesis moved to the *original* polytope and the
warm start built rather than assumed.**

`Ttc.kv97SamplerOfBallWalk` asks for the geometry of the *inflated* body `P'` and for a warm
start on it.  Neither is needed as an input:

* `Arlib.KV97.ball_subset_inflated` and `Arlib.KV97.dist_le_of_mem_inflated`
  (`Arlib/Lattice/KV97/InflateGeom.lean`) transport an inscribed ball `B(cen i, γ i) ⊆ P(cᵢ)`
  and a diameter bound `Dm i` for `P(cᵢ)` to the inflation, at `γ ↦ γ + κ` and
  `D ↦ (1 + κ/γ)·D`;
* `Arlib.MarkovChains.isWarm_uniformOn_inscribed`
  (`Arlib/MarkovChains/Continuous/WarmStartGeneral.lean`) makes the uniform law on that
  inscribed ball a warm start for `P'`, at the *exact* volume ratio.

So the only inputs left are facts about the input polytope itself — an inscribed ball and
boundedness — which are genuine properties of the problem instance (an unbounded or
lower-dimensional `P(cᵢ)` has neither) and are exactly the binders the `Ttc` capstone
already carries.  **Nothing about the sampler is assumed.**

The start is `Arlib.uniformOn volume (Metric.ball (cen i) (γ i + κ))`, which is *not* the
target: see `Ttc.kv97SamplerOfBody_start_ne_target`. -/
noncomputable def kv97SamplerOfBody
    {A : Type*} {n : ℕ} {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ} {epsPrime : ℝ}
    (hn : 1 ≤ n) (hEps : 0 < epsPrime)
    (Jt : Type) [Fintype Jt]
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (hdil : ∀ i, latticeScale ρ • region M i.val ⊆ Arlib.Polytope.body (Am i) (bv i))
    (r : ℝ) (hr1 : 1 ≤ r) (hcard : (Fintype.card Jt : ℝ) ≤ r)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ Dm : {c : Cube A // c ∈ D} → ℝ)
    (hγ : ∀ i, 0 < γ i)
    (hballBody : ∀ i, Metric.ball (cen i) (γ i) ⊆ Arlib.Polytope.body (Am i) (bv i))
    (hDbody : ∀ i, ∀ x ∈ Arlib.Polytope.body (Am i) (bv i),
      ∀ y ∈ Arlib.Polytope.body (Am i) (bv i), dist x y ≤ Dm i)
    (δ : {c : Cube A // c ∈ D} → ℝ) (hδ : ∀ i, 0 < δ i)
    (hδγ : ∀ i, δ i ≤ γ i + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r) :
    KV97Sampler A n M D ρ epsPrime
      (kv97SampD M D ρ (kv97ContLaw epsPrime r Am bv
        (fun i => (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r / γ i) * Dm i)
        (fun i => γ i + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r) δ
        (fun i => (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r) /
          volume (Metric.ball (cen i)
            (γ i + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r))).toReal)
        (fun i => Arlib.uniformOn volume (Metric.ball (cen i)
          (γ i + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r))))) := by
  have hκ : (0 : ℝ) ≤ Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r :=
    Arlib.KV97.kappaOf_nonneg (Arlib.KV97.cOf_nonneg)
  have hγ' : ∀ i, 0 < γ i + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r := fun i => by
    have := hγ i; linarith
  have hball' : ∀ i, Metric.ball (cen i)
      (γ i + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r)
      ⊆ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r := fun i =>
    Arlib.KV97.ball_subset_inflated (hγ i) (hballBody i)
  have hD' : ∀ i, ∀ x ∈ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r,
      ∀ y ∈ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r,
      dist x y ≤ (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r / γ i) * Dm i := fun i =>
    Arlib.KV97.dist_le_of_mem_inflated (hγ i) Arlib.KV97.cOf_nonneg (hballBody i) (hDbody i)
  have hKtop : ∀ i,
      volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r) ≠ ⊤ := fun i =>
    volume_inflated_ne_top (hγ' i) (hball' i) (hD' i)
  have hK0 : ∀ i,
      volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) r) ≠ 0 := fun i =>
    volume_inflated_ne_zero (hγ' i) (hball' i)
  refine kv97SamplerOfBallWalk hn hEps Jt Am bv hdil r hr1 hcard _ hD' cen _ hγ' hball'
    δ hδ hδγ _ (fun i => Arlib.isProbabilityMeasure_uniformOn volume
      (Metric.measure_ball_pos volume _ (hγ' i)).ne' measure_ball_lt_top.ne)
    _ (fun i => Arlib.MarkovChains.one_le_toReal_volume_div_volume_ball
      (hKtop i) (hγ' i) (hball' i)) (fun i => ?_)
  rw [ENNReal.ofReal_toReal
    (Arlib.MarkovChains.volume_div_volume_ball_ne_top (hKtop i) (hγ' i))]
  exact Arlib.MarkovChains.isWarm_uniformOn_inscribed
    (Arlib.KV97.measurableSet_inflated _ _ _ _) (hK0 i) (hKtop i) (hγ' i) (hball' i)

/-- **The start of `Ttc.kv97SamplerOfBody` is not its target.**

`hproper` — the inscribed ball is *strictly* smaller than `P'` in measure — is a real
hypothesis and cannot be dropped: without it the "warm start" could be the stationary
measure itself, and `law_tv` would hold for reasons having nothing to do with mixing.
(Note the inflation helps here: `P'` contains a ball of radius `γ + κ` with `κ > 0`
whenever `0 < ε' < 4`, by `Ttc.kappaOf_cOf_pos`.) -/
theorem kv97SamplerOfBody_start_ne_target {n : ℕ} {ι : Type*} {Am : ι → Space n} {bv : ι → ℝ}
    {epsPrime r : ℝ} {cen : Space n} {γ : ℝ}
    (hγ' : 0 < γ + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r)
    (hball' : Metric.ball cen (γ + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r)
      ⊆ Arlib.KV97.inflated Am bv (Arlib.KV97.cOf epsPrime) r)
    (hK0 : volume (Arlib.KV97.inflated Am bv (Arlib.KV97.cOf epsPrime) r) ≠ 0)
    (hKtop : volume (Arlib.KV97.inflated Am bv (Arlib.KV97.cOf epsPrime) r) ≠ ⊤)
    (hproper : volume (Metric.ball cen (γ + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r))
      < volume (Arlib.KV97.inflated Am bv (Arlib.KV97.cOf epsPrime) r)) :
    Arlib.uniformOn volume
        (Metric.ball cen (γ + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) r))
      ≠ Arlib.uniformOn volume (Arlib.KV97.inflated Am bv (Arlib.KV97.cOf epsPrime) r) :=
  Arlib.MarkovChains.uniformOn_inscribed_ne_uniformOn
    (Arlib.KV97.measurableSet_inflated _ _ _ _) hK0 hKtop hγ' hball' hproper

/-! ## Two generic facts about uniform laws on nested bodies

Used to build a warm start that is demonstrably *not* the target measure. -/

/-- **Uniform on a sub-body is a warm start for uniform on the body**, at the volume ratio
`Vol(K)/Vol(S)`.  The only slack is the inclusion `S ⊆ K`. -/
theorem isWarm_uniformOn_subset {n : ℕ} {S K : Set (Space n)} (hS : MeasurableSet S)
    (hK : MeasurableSet K) (hSK : S ⊆ K) (hS0 : volume S ≠ 0) (hStop : volume S ≠ ⊤)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) :
    Arlib.IsWarm (ENNReal.ofReal ((volume K).toReal / (volume S).toReal))
      (Arlib.uniformOn volume S) (Arlib.uniformOn volume K) := by
  have hcoe : ENNReal.ofReal ((volume K).toReal / (volume S).toReal)
      = volume K / volume S := by
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hS0 hStop),
      ENNReal.ofReal_toReal hKtop, ENNReal.ofReal_toReal hStop]
  intro T hT
  rw [Arlib.uniformOn_apply volume hS hT, Arlib.uniformOn_apply volume hK hT, hcoe]
  have hmul : volume K / volume S * (volume (T ∩ K) / volume K)
      = volume (T ∩ K) / volume S := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      show volume K * (volume S)⁻¹ * (volume (T ∩ K) * (volume K)⁻¹)
        = volume K * (volume K)⁻¹ * (volume (T ∩ K) * (volume S)⁻¹) by ring,
      ENNReal.mul_inv_cancel hK0 hKtop, one_mul]
  rw [hmul]
  exact ENNReal.div_le_div_right
    (measure_mono (Set.inter_subset_inter_right _ hSK)) _

/-- **A strictly smaller sub-body gives a start that is not the target.**  The separating
set is `S` itself: it has mass `1` under `uniformOn volume S` and mass
`Vol(S)/Vol(K) < 1` under `uniformOn volume K`. -/
theorem uniformOn_ne_uniformOn_of_volume_lt {n : ℕ} {S K : Set (Space n)}
    (hS : MeasurableSet S) (hK : MeasurableSet K) (hSK : S ⊆ K) (hS0 : volume S ≠ 0)
    (hStop : volume S ≠ ⊤) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    (hlt : volume S < volume K) :
    Arlib.uniformOn volume S ≠ Arlib.uniformOn volume K := by
  intro heq
  have h1 : Arlib.uniformOn volume S S = 1 := Arlib.uniformOn_self volume hS hS0 hStop
  have h2 : Arlib.uniformOn volume K S = volume S / volume K := by
    rw [Arlib.uniformOn_apply volume hK hS, Set.inter_eq_left.2 hSK]
  rw [heq, h2] at h1
  have : volume S = volume K := by
    rwa [ENNReal.div_eq_one_iff hK0 hKtop] at h1
  exact absurd this hlt.ne

/-! ## Non-vacuity: a fully concrete `KV97Sampler`

The box `{x | ∀ i, |xᵢ| ≤ 1}` and its Kannan–Vempala inflation. -/

section Box

variable {n : ℕ}

/-- The `2n` normals `±eᵢ` of a box, indexed by `Fin n × Bool`. -/
noncomputable def boxNormals (n : ℕ) : Fin n × Bool → Space n := fun p =>
  if p.2 then EuclideanSpace.single p.1 (1 : ℝ) else -EuclideanSpace.single p.1 (1 : ℝ)

/-- Each box normal is a unit vector, so the `κ`-inflation displaces each facet by exactly
`κ`. -/
@[simp] theorem norm_boxNormals (p : Fin n × Bool) : ‖boxNormals n p‖ = 1 := by
  obtain ⟨i, s⟩ := p
  cases s <;> simp [boxNormals]

/-- The two families of box constraints, `+xᵢ ≤ B` and `−xᵢ ≤ B`. -/
theorem inner_boxNormals (p : Fin n × Bool) (x : Space n) :
    inner ℝ (boxNormals n p) x = if p.2 then x p.1 else -x p.1 := by
  obtain ⟨i, s⟩ := p
  cases s <;> simp [boxNormals, EuclideanSpace.inner_single_left, inner_neg_left]

/-- The `κ`-inflation of the box of half-width `B` is the box of half-width `B + κ`. -/
theorem mem_boxInflate {B κ : ℝ} {x : Space n} :
    x ∈ Arlib.Polytope.inflate (boxNormals n) (fun _ => B) κ ↔ ∀ i, |x i| ≤ B + κ := by
  simp only [Arlib.Polytope.mem_inflate, norm_boxNormals, mul_one, inner_boxNormals]
  constructor
  · intro h i
    have h1 := h (i, true)
    have h2 := h (i, false)
    simp only [if_true, if_false, Bool.false_eq_true] at h1 h2
    exact abs_le.2 ⟨by linarith, h1⟩
  · rintro h ⟨i, s⟩
    have hxi := abs_le.1 (h i)
    cases s <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
      linarith [hxi.1, hxi.2]

/-- The un-inflated box: `x ∈ body ↔ ∀ i, |xᵢ| ≤ B`. -/
theorem mem_boxBody {B : ℝ} {x : Space n} :
    x ∈ Arlib.Polytope.body (boxNormals n) (fun _ => B) ↔ ∀ i, |x i| ≤ B := by
  rw [← Arlib.Polytope.inflate_zero (boxNormals n) (fun _ => B)]
  simpa using (mem_boxInflate (B := B) (κ := 0) (x := x))

/-- A ball of radius at most the half-width sits inside the inflated box. -/
theorem ball_subset_boxInflate {B κ R : ℝ} (hR : R ≤ B + κ) :
    Metric.ball (0 : Space n) R ⊆ Arlib.Polytope.inflate (boxNormals n) (fun _ => B) κ := by
  intro x hx
  have hxn : ‖x‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hx
  refine mem_boxInflate.2 fun i => ?_
  have hle := PiLp.norm_apply_le (p := 2) x i
  rw [Real.norm_eq_abs] at hle
  linarith

/-- The inflated box has diameter at most `2(B+κ)√n`. -/
theorem dist_le_of_mem_boxInflate {B κ : ℝ} (hBκ : 0 ≤ B + κ) :
    ∀ x ∈ Arlib.Polytope.inflate (boxNormals n) (fun _ => B) κ,
      ∀ y ∈ Arlib.Polytope.inflate (boxNormals n) (fun _ => B) κ,
        dist x y ≤ 2 * (B + κ) * Real.sqrt n := by
  intro x hx y hy
  have hxi := mem_boxInflate.1 hx
  have hyi := mem_boxInflate.1 hy
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ 4 * (B + κ) ^ 2 * (n : ℝ) := by
    have hle : ∀ i ∈ Finset.univ, dist (x i) (y i) ^ 2 ≤ 4 * (B + κ) ^ 2 := by
      intro i _
      have h1 := abs_le.1 (hxi i)
      have h2 := abs_le.1 (hyi i)
      have hd : dist (x i) (y i) = |x i - y i| := Real.dist_eq _ _
      rw [hd, sq_abs]
      nlinarith [h1.1, h1.2, h2.1, h2.2]
    calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin n, (4 * (B + κ) ^ 2) := Finset.sum_le_sum hle
      _ = 4 * (B + κ) ^ 2 * (n : ℝ) := by simp [mul_comm]
  calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt (4 * (B + κ) ^ 2 * (n : ℝ)) :=
        Real.sqrt_le_sqrt hsum
    _ = 2 * (B + κ) * Real.sqrt n := by
        rw [Real.sqrt_mul (by positivity),
          show (4 : ℝ) * (B + κ) ^ 2 = (2 * (B + κ)) ^ 2 by ring,
          Real.sqrt_sq (by linarith)]

/-- `Arlib.KV97.cOf ε` is **strictly** positive for `0 < ε < 4`; the inflation displacement
`κ = cOf ε + √(2 log r)` is therefore strictly positive too, which is what makes the
inflated box strictly larger than the inscribed unit ball. -/
theorem cOf_pos {ε : ℝ} (hε0 : 0 < ε) (hε4 : ε < 4) : 0 < Arlib.KV97.cOf ε := by
  refine Real.sqrt_pos.2 ?_
  have : (1 : ℝ) < 4 / ε := (one_lt_div hε0).2 hε4
  have := Real.log_pos this
  linarith

/-- Hence `0 < kappaOf (cOf ε) r` whenever `0 < ε < 4`. -/
theorem kappaOf_cOf_pos {ε r : ℝ} (hε0 : 0 < ε) (hε4 : ε < 4) :
    0 < Arlib.KV97.kappaOf (Arlib.KV97.cOf ε) r := by
  have h := cOf_pos hε0 hε4
  have h2 : (0 : ℝ) ≤ Real.sqrt (2 * Real.log r) := Real.sqrt_nonneg _
  rw [Arlib.KV97.kappaOf]
  linarith

end Box

/-! ## The non-vacuity witness

`CLAUDE.md` §11: a construction that is inhabited only at degenerate parameters certifies
nothing, and the specific degeneracy to rule out here is `contLaw = uniformOn volume P'`,
which would make `law_tv` a restatement of `Arlib.TVLe.refl`.

The witness below is a genuine `Ttc.KV97Sampler` on the box `{x | ∀ i, |xᵢ| ≤ 1}` (one
atom, one cube, `ρ = 0`, `2n` facets), and it carries three conjuncts that the degenerate
construction could not supply:

* `0 < ε'` — the accuracy parameter is not zero;
* `ENNReal.ofReal (ε'/(4·contVol i)) ≤ ENNReal.ofReal (1/2)` — the total-variation
  tolerance is **at most `1/2`, hence not the vacuous `≥ 1`**, so `law_tv` really
  constrains the law.  (This is why `ε'` is taken to be `min (1/12) (2·Vol(B₁))`: the
  tolerance carries a `1/Vol(P')`, so a fixed `ε'` with a tiny body would be vacuous.)
* the law is an `iterate` of the lazy ball-walk kernel applied to a start `mu0` which is
  proved **different from the target** `Arlib.uniformOn volume P'`.

What is *not* claimed: that the `t`-step law itself differs from the target.  See the
module docstring. -/
theorem exists_kv97Sampler_box (n : ℕ) (hn : 1 ≤ n) :
    ∃ (epsPrime : ℝ) (sampD : Cube Unit → Space n → ℝ)
      (S : KV97Sampler Unit n (fun _ => Metric.closedBall 0 (1 / 2))
        [[(⟨(), true⟩ : Lit Unit)]] 0 epsPrime sampD),
      0 < epsPrime ∧
      Nonempty {c : Cube Unit // c ∈ [[(⟨(), true⟩ : Lit Unit)]]} ∧
      ∀ i, ENNReal.ofReal (epsPrime / (4 * S.contVol i)) ≤ ENNReal.ofReal (1 / 2) ∧
        ∃ (mu0 : Measure (Space n)) (t : ℕ),
          S.contLaw i = Arlib.MarkovChains.iterate
            (Arlib.MarkovChains.lazy (Arlib.MarkovChains.ballWalk
              (Arlib.KV97.inflated (S.Amat i) (S.bvec i) (Arlib.KV97.cOf epsPrime)
                S.facetBound) 1)) mu0 t ∧
          mu0 ≠ Arlib.uniformOn volume
            (Arlib.KV97.inflated (S.Amat i) (S.bvec i) (Arlib.KV97.cOf epsPrime)
              S.facetBound) := by
  classical
  -- the inscribed unit ball, and its volume
  have hb0 : volume (Metric.ball (0 : Space n) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hbtop : volume (Metric.ball (0 : Space n) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hv0 : 0 < (volume (Metric.ball (0 : Space n) 1)).toReal := ENNReal.toReal_pos hb0 hbtop
  -- the accuracy parameter: positive, at most `1/12`, and small compared to the volume
  set ep : ℝ := min (1 / 12) (2 * (volume (Metric.ball (0 : Space n) 1)).toReal) with hepdef
  have hep0 : 0 < ep := lt_min (by norm_num) (by linarith)
  have hep4 : ep < 4 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  set rr : ℝ := max 1 (2 * (n : ℝ)) with hrrdef
  have hr1 : (1 : ℝ) ≤ rr := le_max_left _ _
  have hk0 : 0 < Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr := kappaOf_cOf_pos hep0 hep4
  -- the body: the `κ`-inflation of the box of half-width `1`
  set K : Set (Space n) :=
    Arlib.KV97.inflated (boxNormals n) (fun _ => (1 : ℝ)) (Arlib.KV97.cOf ep) rr with hKdef
  have hKmeas : MeasurableSet K := Arlib.KV97.measurableSet_inflated _ _ _ _
  have hball1 : Metric.ball (0 : Space n) 1 ⊆ K := ball_subset_boxInflate (by linarith)
  have hballBig : Metric.ball (0 : Space n) (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) ⊆ K :=
    ball_subset_boxInflate le_rfl
  have hDK : ∀ x ∈ K, ∀ y ∈ K,
      dist x y ≤ 2 * (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) * Real.sqrt n :=
    dist_le_of_mem_boxInflate (by linarith)
  have hK0 : volume K ≠ 0 := Arlib.MarkovChains.volume_ne_zero_of_ball_subset one_pos hball1
  have hKtop : volume K ≠ ⊤ :=
    Arlib.MarkovChains.volume_ne_top_of_diam_bound (hball1 (Metric.mem_ball_self one_pos)) hDK
  -- the body is strictly bigger than the inscribed unit ball
  have hvolLt : volume (Metric.ball (0 : Space n) 1) < volume K := by
    refine lt_of_lt_of_le ?_ (measure_mono hballBig)
    have hbig := MeasureTheory.Measure.addHaar_ball_of_pos (volume : Measure (Space n)) 0
      (show (0 : ℝ) < 1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr by linarith)
    rw [finrank_euclideanSpace_fin] at hbig
    rw [hbig]
    have h1 : (1 : ℝ) < (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) ^ n :=
      one_lt_pow₀ (by linarith) (by omega)
    have h2 : (1 : ℝ≥0∞)
        < ENNReal.ofReal ((1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) ^ n) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 h1
    calc volume (Metric.ball (0 : Space n) 1)
        = volume (Metric.ball (0 : Space n) 1) * 1 := (mul_one _).symm
      _ < volume (Metric.ball (0 : Space n) 1)
            * ENNReal.ofReal ((1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) ^ n) :=
          ENNReal.mul_lt_mul_right hb0 hbtop h2
      _ = _ := mul_comm _ _
  have hvle : (volume (Metric.ball (0 : Space n) 1)).toReal ≤ (volume K).toReal :=
    (ENNReal.toReal_le_toReal hbtop hKtop).2 hvolLt.le
  have hKpos : 0 < (volume K).toReal := lt_of_lt_of_le hv0 hvle
  -- the warm start: uniform on the inscribed unit ball
  haveI hmu0 : IsProbabilityMeasure (Arlib.uniformOn volume (Metric.ball (0 : Space n) 1)) :=
    Arlib.isProbabilityMeasure_uniformOn volume hb0 hbtop
  have hMw1 : (1 : ℝ)
      ≤ (volume K).toReal / (volume (Metric.ball (0 : Space n) 1)).toReal := by
    rw [le_div_iff₀ hv0]; linarith
  have hwarm := isWarm_uniformOn_subset measurableSet_ball hKmeas hball1 hb0 hbtop hK0 hKtop
  -- the linear description contains the (undilated) region
  have hdil : ∀ i : {c : Cube Unit // c ∈ [[(⟨(), true⟩ : Lit Unit)]]},
      latticeScale (0 : ℤ) • region (fun _ => Metric.closedBall (0 : Space n) (1 / 2)) i.val
        ⊆ Arlib.Polytope.body (boxNormals n) (fun _ => (1 : ℝ)) := by
    intro i
    have hls : latticeScale (0 : ℤ) = (1 : ℝ) := by simp [latticeScale]
    rw [hls, one_smul]
    have hival : i.val = [(⟨(), true⟩ : Lit Unit)] := by simpa using i.2
    rw [hival]
    intro x hx
    have hmem : x ∈ Metric.closedBall (0 : Space n) (1 / 2) := by
      simpa [region, Cube.holds, Lit.holds, induced] using hx
    have hxn : ‖x‖ ≤ 1 / 2 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hmem
    refine mem_boxBody.2 fun j => ?_
    have hle := PiLp.norm_apply_le (p := 2) x j
    rw [Real.norm_eq_abs] at hle
    linarith
  have hcard : ((Fintype.card (Fin n × Bool) : ℕ) : ℝ) ≤ rr := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
      Nat.cast_ofNat]
    have : (2 : ℝ) * (n : ℝ) ≤ rr := le_max_right _ _
    linarith
  -- the sampler
  refine ⟨ep, _, kv97SamplerOfBallWalk hn hep0 (Fin n × Bool)
    (fun _ => boxNormals n) (fun _ _ => (1 : ℝ)) hdil rr hr1 hcard
    (fun _ => 2 * (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf ep) rr) * Real.sqrt n)
    (fun _ => hDK) (fun _ => 0) (fun _ => 1) (fun _ => one_pos) (fun _ => hball1)
    (fun _ => 1) (fun _ => one_pos) (fun _ => le_rfl)
    (fun _ => Arlib.uniformOn volume (Metric.ball (0 : Space n) 1)) (fun _ => hmu0)
    (fun _ => (volume K).toReal / (volume (Metric.ball (0 : Space n) 1)).toReal)
    (fun _ => hMw1) (fun _ => hwarm),
    hep0, ⟨⟨[(⟨(), true⟩ : Lit Unit)], by simp⟩⟩, ?_⟩
  intro i
  refine ⟨?_, _, _, rfl, ?_⟩
  · show ENNReal.ofReal (ep / (4 * (volume K).toReal)) ≤ ENNReal.ofReal (1 / 2)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have : ep ≤ 2 * (volume (Metric.ball (0 : Space n) 1)).toReal := min_le_right _ _
    linarith
  · exact uniformOn_ne_uniformOn_of_volume_lt measurableSet_ball hKmeas hball1 hb0 hbtop
      hK0 hKtop hvolLt

/-! ### Axiom audit (`CLAUDE.md` §4)

Every declaration in this file must depend on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms mixSteps
#print axioms ballWalkLaw
#print axioms ballWalkLaw_eq_iterate
#print axioms ballWalkLaw_zero
#print axioms isProbabilityMeasure_ballWalkLaw
#print axioms tvLe_ballWalkLaw_inflated
#print axioms volume_inflated_ne_zero
#print axioms volume_inflated_ne_top
#print axioms toReal_volume_inflated_pos
#print axioms kv97SampD
#print axioms kv97SampD_apply
#print axioms kv97ContLaw
#print axioms kv97ContLaw_eq_iterate
#print axioms kv97SamplerOfBallWalk
#print axioms kv97SamplerOfBody
#print axioms kv97SamplerOfBody_start_ne_target
#print axioms isWarm_uniformOn_subset
#print axioms uniformOn_ne_uniformOn_of_volume_lt
#print axioms boxNormals
#print axioms norm_boxNormals
#print axioms inner_boxNormals
#print axioms mem_boxInflate
#print axioms mem_boxBody
#print axioms ball_subset_boxInflate
#print axioms dist_le_of_mem_boxInflate
#print axioms cOf_pos
#print axioms kappaOf_cOf_pos
#print axioms exists_kv97Sampler_box

end Ttc
