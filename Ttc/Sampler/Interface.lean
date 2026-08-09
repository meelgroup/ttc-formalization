/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Prelude
import Arlib.Lattice.KV97.Theorem2
import Arlib.Probability.TV
import Arlib.Probability.UniformOn

/-!
# `Sampler/Interface`: `GenerateSamples`' construction, as Kannan-Vempala's sampler

`Ttc.KV97Sampler` is the description of the sampler that `Ttc.TtcProb.sampler`
carries. It is declared here rather than in `Model/ProblemSetting`, which holds
the paper's problem setting and nothing else.
-/

namespace Ttc

open MeasureTheory Pointwise

/-! ## `GenerateSamples`' construction, as Kannan–Vempala's sampler

The paper's contract for `GenerateSamples` is `eq:almostuniform`
(`sections/related.tex:21`): the law it returns on `P(cᵢ) ∩ 𝕃ⁿ` is within a
multiplicative `(1 ± ε')` of uniform. That used to be a `Ttc.TtcProb` field,
assumed outright. It no longer is.

What is assumed instead is *how the sampler is built* — the construction
Kannan–Vempala's Theorem 2 analyses:

1. dilate `P(cᵢ)` by `10^ρ`, so that `𝕃ⁿ`-points become `ℤⁿ`-points, and record
   a linear description `A x ≤ b` of a body containing it (`dilate_eq`);
2. inflate it to `P'` by the metric displacement `κ = c + √(2 log r)`,
   `c = √(2 log(4/ε'))` (`Arlib.KV97.inflated`);
3. draw a *continuous* point `p ∈ P'` from a law `contLaw` that is within
   **total variation** `ε'/(4·Vol(P'))` of uniform on `P'` (`law_tv`) — this is
   what a mixed Markov chain such as the ball walk delivers;
4. round `p` to a lattice point by randomized rounding (the product tent kernel
   `Arlib.Lattice.Rounding.prodTent`);
5. reject and renormalise onto the integer points of the dilated body
   (`sampD_eq`).

`eq:almostuniform` is then a **theorem** — `Ttc.TtcProb.samp_unif`
(`Ttc/Sampler/Bridge.lean`), proved by `Ttc.almostUniform_of_kv97_density`, which
composes `Arlib.KV97.theorem2` with the `ℤⁿ → 𝕃ⁿ` transport. Nothing about the
*rate* at which the sampler mixes, or its failure probability, is assumed or
needed: only the shape of the law it returns.

**What is not a field.** The escape-mass hypothesis of `Arlib.KV97.theorem2` —
that the rounding kernel puts at most `exp(−c²/2)` outside `P'` — is *not*
assumed: `Arlib.Lattice.Rounding.setIntegral_prodTent_compl_inflate_le_exp`
proves it for any lattice point of the body, and `dilate_eq` says the enumerated
points are lattice points of the body. `Ttc.escape_of_mem_body`
(`Ttc/Sampler/Bridge.lean`) is the discharge. -/

/-- **The Kannan–Vempala realisation of `GenerateSamples`**, per cube of the DNF.

`sampD` is the discrete law the sampler returns; this structure says that law is
the rejection-normalised randomized rounding of a nearly-uniform continuous draw
from the inflated dilated polytope, which is exactly the object
`Arlib.KV97.theorem2` analyses.

Only one index type is carried: `J`, enumerating the facets of the dilated body.
The integer points of the dilated body are *not* carried — the rejection sum in
`sampD_eq` is a `finsum` over the set `10^ρ·P(cᵢ) ∩ ℤⁿ` itself, so no `Fintype`
has to be assumed. `KV97Sampler` on its own has no access to the geometry that
would make that set finite (boundedness of `region M i` is a `Ttc.TtcProb`
field, not one of this structure's), which is exactly why the finiteness is left
to the consumer, where it is *proved*
(`Ttc.TtcProb.dilate_intLattice_finite`).

## Why the hypothesis is total-variation and not pointwise

This structure used to carry a *density* `contDensity` together with
`density_au : Arlib.KV97.PointwiseAlmostUniform (contDensity i) P' (contVol i)
(ε'/4)` — a **pointwise** almost-uniformity bound — and an integrability guard
`density_int`. Those three fields are gone, replaced by the law `contLaw` and
the total-variation bound `law_tv`. The reason is not convenience:

* **The pointwise hypothesis is unattainable for the chain the algorithm runs.**
  `Arlib.KV97.PointwiseAlmostUniform` presupposes the sampler's law has a
  density, and a ball-walk law started at a point never does — the holding term
  `(1 − ℓ(x))·δ_x` keeps an atom forever. One atom defeats pointwise closeness
  for **every** `ε`, `⊤` included
  (`Arlib.PointwiseRoute.not_pointwiseClose_of_atom`), while a total-variation
  bound tolerates it (`Arlib.PointwiseRoute.exists_tvLe_with_atom`). So
  `density_au` was on a path the real sampler cannot walk.
* **The total-variation hypothesis is attainable and it is enough.**
  `AUDIT-KV97.md` §4b used to conclude the opposite, on the ground that a TV
  bound buys only an *additive* error; the boxed correction there retracts it.
  An additive error `ε` **is** a relative error `ε·V`, so asking the sampler for
  tolerance `θ/Vol(P')` rather than `θ` delivers exactly the window Theorem 2
  needs (`Arlib.PointwiseRoute.window_of_tvLe`), and mixing time is
  *logarithmic* in the tolerance, so the extra `1/V` costs only `+2 log V/φ²`
  steps (`Arlib.PointwiseRoute.conductanceMixingTime_inv_volume_le`).
* Both Kannan–Vempala ("variational distance to the uniform density") and the
  consuming paper ("`ε`-close to uniform over `P'` in TV distance") say total
  variation. What neither states is the `1/Vol(P')` scaling of the tolerance,
  which `law_tv` carries explicitly.

**`contVol` is no longer a gauge.** Under the density formulation the normaliser
cancelled out of `sampD` — `contVol` could be moved to any positive value
without changing the sampler's law, which is what the deleted
`Ttc.KV97Sampler.reNormalise` proved. That is a fact about the *density*
formulation and it does **not** survive: here the tolerance `ε'/(4·contVol i)`
couples to `contVol`, and `contVol_eq` pins it to `(Vol P')`. So `contVol` is now
a **determined** quantity, not a free one, and the two side conditions
`Vol(P') ≠ 0`, `Vol(P') ≠ ∞` that `Arlib.PointwiseRoute.theorem2_of_tvLe` needs
come out of `contVol_pos` and `contVol_eq` together (`0 < x.toReal` forces
`x ∉ {0, ∞}`). Nothing extra is assumed for them.

## Three fields that were weaker, or more derivable, than they looked

An audit of this structure raised four questions; the fourth (`density_int`) is
moot now that the field is gone. The other three are settled, and the answers
live in `Ttc/Sampler/Bridge.lean`.

1. **`dilate_eq` was an equality; only `⊆` is used.** *Fixed.* The field is now
   the inclusion `10^ρ·P(cᵢ) ⊆ body(A,b)`, which is exactly what
   `Ttc.KV97Sampler.dilate_subset` (the name the proof routes through) needs.
2. **`idx`/`fintypeIdx`/`nonemptyIdx`/`enum` were derivable, not assumed.**
   *Fixed:* all four are **gone**. `Ttc.TtcProb.exists_idx_enum` had already
   shown any `Ttc.TtcProb` can build them from `ball_subset`, `volume_ne_top`
   and the proved `lem:lattice`; the sum in `sampD_eq` is now a `finsum` over
   `10^ρ·P(cᵢ) ∩ ℤⁿ` itself, and the consumer
   (`Ttc.TtcProb.samp_almostUniform_subtype`) supplies the `Fintype` and the
   `Nonempty` from `Ttc.TtcProb.dilate_intLattice_finite` and
   `Ttc.TtcProb.dilate_intLattice_nonempty` — both theorems, neither a field.
3. **`density_int` is gone rather than justified.** Integrability was a genuine
   assumption under the density formulation, because a pointwise *band*
   condition carries no measurability. Under `contLaw` there is nothing to
   assume: `prodTent` is bounded and measurable and `contLaw i` is a probability
   measure, so `∫ p, prodTent z p ∂(contLaw i)` always exists.

## What the arithmetic downstream had to change

*The tuned constants are not reusable.* The pointwise route handed
`Ttc.almostUniform_of_kv97` the window `[(1−ε/4)(1−E)/V, (1+ε/4)/V]`, and
`Arlib.KV97.ratio_bounds_tuned_sharp` is tuned to exactly that. The TV route
produces `[(1−(E+θ))/V, (1+θ)/V]` instead — **weaker on the low side** by `θ·E`,
since `(1−θ)(1−E) = 1−E−θ+θE`. So it goes through
`Arlib.Rejection.ratio_bounds_of_window` directly
(`Ttc.almostUniform_of_kv97_window`), not through `ratio_bounds_tuned_sharp`.

*The tuning constant changes from `5/8` to `1/2`.* With `θ = ε'/4` and
`E = exp(−(cOf ε')²/2) = ε'/4` (`Arlib.KV97.exp_cOf`), the window is
`a = ε'/2`, `b = ε'/4`, and `ratio_bounds_of_window` gives
`[(1−a)/((1+b)N), (1+b)/((1−a)N)]`. Reaching `eq:almostuniform` at `ε'` needs
`(1−ε')(1+b) ≤ 1−a` — free for `ε' ≥ 0` — and `(1+b) ≤ (1+ε')(1−a)`, which
reduces to **`ε' ≤ 1/2`**, not the `5/8` that
`Ttc.TtcProb.epsPrime_le_five_eighths` supplies.
`Ttc.TtcProb.epsPrime_le_one_half` is the lemma; since `ε' = ε/12 ≤ 1/12` it is
free. -/
structure KV97Sampler (A : Type*) (n : ℕ) (M : A → Set (Space n)) (D : DNF A) (ρ : ℤ)
    (epsPrime : ℝ) (sampD : Cube A → Space n → ℝ) where
  /-- The facet index of the dilated polytopes. -/
  J : Type
  /-- There are finitely many facets. -/
  [fintypeJ : Fintype J]
  /-- The normals of the *dilated* polytope `10^ρ · P(cᵢ)`. -/
  Amat : {c : Cube A // c ∈ D} → J → Space n
  /-- Its offsets. -/
  bvec : {c : Cube A // c ∈ D} → J → ℝ
  /-- **The linear description contains the dilated polytope.** This is the field
  that stops `Amat`/`bvec` being a free linear system: the body they cut out
  contains `10^ρ · P(cᵢ)`, whose integer points are the algorithm's `𝕃ⁿ`-points,
  so every enumerated point is a lattice point of the body and the escape
  estimate applies to it.

  **This is exactly what the proof consumes, no more.** It used to be the
  *equality* `body(A,b) = 10^ρ·P(cᵢ)`, but the one consumer,
  `Ttc.TtcProb.samp_almostUniform_subtype`, uses only this inclusion (via
  `Ttc.escape_of_mem_body`), so the equality was a gratuitously strong
  hypothesis. `Ttc.KV97Sampler.dilate_subset` is now the identity on this field
  and remains the name the proof routes through. -/
  dilate_eq : ∀ i, latticeScale ρ • region M i.val ⊆ Arlib.Polytope.body (Amat i) (bvec i)
  /-- `r`, Kannan–Vempala's facet-count bound; it fixes the inflation
  `κ = c + √(2 log r)`. -/
  facetBound : ℝ
  /-- `r ≥ 1`, so `√(2 log r)` is real. -/
  one_le_facetBound : 1 ≤ facetBound
  /-- `r` really bounds the facet count — what pays for the union bound over
  facets in the escape estimate. -/
  card_le_facetBound : (Fintype.card J : ℝ) ≤ facetBound
  /-- **The law of the continuous draw**, on the inflated dilated polytope.

  A *measure*, not a density: the law a Markov chain reaches need not be
  absolutely continuous, and for the ball walk started at a point it provably is
  not (`Arlib.PointwiseRoute.not_pointwiseClose_of_atom`). This is the field
  that used to be `contDensity`. -/
  contLaw : {c : Cube A // c ∈ D} → MeasureTheory.Measure (Space n)
  /-- The sampler returns a point, so its law is a probability measure. -/
  isProbContLaw : ∀ i, MeasureTheory.IsProbabilityMeasure (contLaw i)
  /-- `Vol(P')`, the volume the tolerance in `law_tv` is measured against.

  **It is pinned by `contVol_eq`, and under this formulation it has to be.**
  Under the old density formulation the normaliser was a *gauge* — it cancelled
  out of `sampD` and could be moved anywhere. Here it cannot: `law_tv`'s
  tolerance is `ε'/(4·contVol i)`, so `contVol` is part of the hypothesis's
  strength. Keeping it as a field with an equation, rather than writing
  `(volume (inflated …)).toReal` inline, is what lets `contVol_pos` deliver the
  two side conditions `Vol(P') ≠ 0` and `Vol(P') ≠ ∞` in one stroke. -/
  contVol : {c : Cube A // c ∈ D} → ℝ
  /-- It is positive. With `contVol_eq` this is exactly `0 < Vol(P') < ∞`, which
  is what `Arlib.PointwiseRoute.theorem2_of_tvLe` asks for. -/
  contVol_pos : ∀ i, 0 < contVol i
  /-- **`contVol` really is `Vol(P')`.** Not a normalisation convention: the
  tolerance `ε'/(4·contVol i)` is only the right one if `contVol` is the volume
  the uniform reference law is spread over. -/
  contVol_eq : ∀ i, contVol i =
    (MeasureTheory.volume (Arlib.KV97.inflated (Amat i) (bvec i)
      (Arlib.KV97.cOf epsPrime) facetBound)).toReal
  /-- **The continuous draw is within total variation `ε'/(4·Vol(P'))` of uniform
  on the inflated polytope.**

  This is what a mixing bound delivers, and — unlike the pointwise bound it
  replaces — it is attainable by a law with atoms. The `1/Vol(P')` in the
  tolerance is the whole content of `AUDIT-KV97.md` §4b's correction: an additive
  TV error `ε` is a relative error `ε·Vol(P')`, so the tolerance must carry the
  `1/Vol(P')` for the `ε`s to cancel in `cor:linf`. Mixing time is logarithmic in
  the tolerance, so this costs `O(log Vol(P')/φ²)` extra steps and nothing
  else. -/
  law_tv : ∀ i, Arlib.TVLe (contLaw i)
    (Arlib.uniformOn MeasureTheory.volume
      (Arlib.KV97.inflated (Amat i) (bvec i) (Arlib.KV97.cOf epsPrime) facetBound))
    (ENNReal.ofReal (epsPrime / (4 * contVol i)))
  /-- **The sampler's law is the rejection-normalised rounding law.** The mass at
  a fine-lattice point `x` of `P(cᵢ)` is the probability that rounding the
  continuous draw lands on the dilated point `10^ρ · x`, conditioned on landing
  in the dilated polytope at all. This is the *definition* of the sampler, not a
  bound on it.

  **The denominator is a `∑ᶠ`, and that is what lets the enumeration fields go.**
  The rejection sum runs over the integer points of the dilated polytope; writing
  it as `Finset.sum` would need a `Fintype` on that set, which this structure
  cannot produce — boundedness of `region M i` is a `Ttc.TtcProb` field, not one
  of this structure's. `finsum` needs no such instance, and where the count *is*
  finite (which `Ttc.TtcProb.dilate_intLattice_finite` proves, from
  `ball_subset`/`volume_ne_top`) `finsum_eq_sum_of_fintype` turns it back
  into the ordinary sum. -/
  sampD_eq : ∀ i, ∀ x ∈ region M i.val ∩ fineLattice n (latticeScale ρ),
    sampD i.val x =
      (∫ p, Arlib.Lattice.Rounding.prodTent (latticeScale ρ • x) p ∂(contLaw i)) /
        ∑ᶠ k : ((latticeScale ρ • region M i.val) ∩ intLattice n : Set (Space n)),
          ∫ p, Arlib.Lattice.Rounding.prodTent (k : Space n) p ∂(contLaw i)

attribute [instance] KV97Sampler.fintypeJ

end Ttc
