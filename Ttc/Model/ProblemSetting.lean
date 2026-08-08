/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Dnf
import Ttc.Runtime
import Ttc.Coupling.Family
import Ttc.Process.SketchProcess
import Ttc.Lattice.Decomposition
import Arlib.Lattice.KV97.Theorem2
import Arlib.Probability.TV
import Arlib.Probability.UniformOn

/-!
# `Model/ProblemSetting`: the problem, and everything assumed about it

`Ttc.TtcProb` is the whole hypothesis surface of the development: the input
formula, the run, the probability space its randomness lives in, and a
description of the sampler. `Model/Theorem` quantifies over it and adds nothing.

**No lemma of the paper is assumed here.** `lem:lattice` is *proved* from the
geometric fields (`Ttc.TtcProb.lattice_lo`, `Ttc.TtcProb.lattice_hi`, in
`Lattice/Assembled`); `lem:numlattice` is *proved* from the sampler
fields (`Ttc.TtcProb.numlattice_union`, hence `Ttc.TtcProb.numlattice`, in
`Coupling/Transfer` and `Coupling/NumLattice`).

What the fields assume is what the paper assumes of its *input* — that the atoms
are linear, that each polytope contains an inscribed ball of radius `γ̂` and has
finite volume, that the DNF has no negated literal — plus, of its *sampler*, that
the randomness is the Poisson/thinning family of `Coupling/Family`.
-/

namespace Ttc

open MeasureTheory Pointwise

/-! ## `Vol_ED`'s contract, stated as Cousins–Vempala Theorem 1.1

`Ttc.Oracles.vol` is the `Vol_ED(P(cᵢ), ε', δ')` call of `alg:ttc` line 24. Its
guarantee used to be a single `Ttc.TtcProb` field,

```
volED_hi : ∀ i ∈ toDNF φ, vol i ≤ (1 + P.epsPrime) * (volume (region M i)).toReal
```

which was **deterministic** — it asserted the bound at every `ω`, i.e. that
`Vol_ED` never fails — and so was strictly stronger than what any randomized
volume algorithm delivers. That field is gone; what replaces it is the published
contract it was supposed to be an instance of:

> **Theorem 1.1** (Cousins–Vempala, `vol3_journal.tex:144`). There is an
> algorithm that, for any `ε > 0`, `p > 0` and convex body `K` in `ℝⁿ` that
> contains the unit ball and has `E_K(‖X‖²) = O(n)`, with probability `1 − p`,
> approximates the volume of `K` within relative error `ε`.

**Nothing here proves it.** This is an *interface* in the sense of `CLAUDE.md`
§1: the hypothesis bundle a future formalization instantiates. See
[`CV-ROADMAP.md`](../../CV-ROADMAP.md) for what closing it involves, and
[`END-TO-END-PLAN.md`](../../END-TO-END-PLAN.md) Phase 5 for the plan.

Everything *proved* about it — the rounding bridge that discharges Theorem 1.1's
"contains the unit ball" hypothesis, the union bound over the `m` calls, and the
former field recovered as a theorem — lives in `Ttc/Volume/Bridge.lean`, so that
this file stays what it claims to be: declarations and assumptions, no proofs.

**Modelling notes.**

*The second-moment hypothesis is omitted from `correct`.* Theorem 1.1 states
`E_K(‖X‖²) = O(n)`, but that hypothesis governs the *complexity*, not the
accuracy: `vol3_journal.tex:152` gives the complexity for a general
`E_K(‖X‖²) = R²`, with the same `1 − p` accuracy conclusion. Since only accuracy
is consumed here, assuming it would weaken the interface for no gain. Complexity
is out of scope (`Ttc/Runtime.lean`).

*`K` must contain the unit ball at the origin.* That is Theorem 1.1's hypothesis
verbatim, and it is **not** what `Ttc.TtcProb` supplies: `ball_subset` gives a
ball of radius `γ̂` about `cen i`. `Ttc.VolumeAlgorithm.of_ball`
(`Ttc/Volume/Bridge.lean`) bridges the gap by scaling along `Ttc.roundBody`, and
is where that discrepancy is discharged rather than hidden. -/

/-- **Cousins–Vempala, Theorem 1.1** (`vol3_journal.tex:144`), as the contract
`Vol_ED` is called under.

`est K ε p ω` is the number the algorithm returns on body `K` at accuracy `ε` and
confidence `p`, when its coins read `ω`. `correct` is the theorem: outside a set
of measure `p`, that number lies in `(1 ± ε)·Vol(K)`.

This is an assumption, not a theorem — see the section docstring. -/
structure VolumeAlgorithm (n : ℕ) where
  /-- The probability space the algorithm's own coins live on. -/
  Ω : Type
  /-- Its σ-algebra. -/
  mΩ : MeasurableSpace Ω
  /-- The law of the coins. -/
  μ : @MeasureTheory.Measure Ω mΩ
  /-- It is a probability measure. -/
  isProb : @MeasureTheory.IsProbabilityMeasure Ω mΩ μ
  /-- The estimate returned on `K` at accuracy `ε`, confidence `p`, coins `ω`. -/
  est : Set (Space n) → ℝ → ℝ → Ω → ℝ
  /-- **The estimate is a measurable function of the coins.** Not part of the
  paper's statement, and not a mathematical assumption about the algorithm: it is
  what makes "the failure event" a set with a measure at all. Without it the
  *complement* of the good event has no upper bound — subadditivity alone gives
  `1 ≤ μ(S) + μ(Sᶜ)`, the wrong direction — so the `m` calls of `alg:ttc` could
  not be union-bounded. Any algorithm reading finitely many coins satisfies it. -/
  est_meas : ∀ (K : Set (Space n)) (ε p : ℝ), @Measurable Ω ℝ mΩ _ (est K ε p)
  /-- **The guarantee.** With probability at least `1 − p`, the estimate lies
  within relative error `ε` of `Vol(K)`, for every convex `K` of finite volume
  containing the unit ball. -/
  correct : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 →
      Convex ℝ K → Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      1 - p ≤ (μ {ω | est K ε p ω ∈ relErr ε (volume K).toReal}).toReal

/-- **The good event of the `m` `Vol_ED` calls**: every call's rescaled estimate
lands within a relative `ε'` of its polytope's volume.

Indexed by position in the DNF, so `m` is literally the loop count of `alg:ttc`
line 23. `cen j` and `γ` describe the inscribed ball of `K j`; the estimate is the
one Theorem 1.1 delivers on the *normalised* body `Ttc.roundBody`, rescaled by
`γⁿ` (`Ttc.VolumeAlgorithm.of_ball`). -/
def volGood {n m : ℕ} (V : VolumeAlgorithm n) (γ ε' δ' : ℝ)
    (cen : Fin m → Space n) (K : Fin m → Set (Space n)) : Set V.Ω :=
  {ω | ∀ j, γ ^ n * V.est (roundBody (cen j) γ (K j)) ε' δ' ω
        ∈ relErr ε' (volume (K j)).toReal}

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

/-- The problem instance, the run, and the assumptions.

| Field | Paper | Status |
| --- | --- | --- |
| `isDNF` | `ToDNF`/AllSAT is correct | assumed of the external tool; `thm:decomposition` is *proved* from it |
| `ball_subset`, `volume_ne_top`, `isPositive`, `normal_ne_zero` | `lem:nonconv`'s hypotheses | assumed of the *input*; `lem:lattice` is **proved** from them (`Lattice/Assembled`) |
| `law_eq`, `oracle_eq`, `sampler`, `theta_eq`, … | the sampler is the Poisson/thinning family, drawing by Kannan–Vempala rounding | assumed of the *sampler*; `lem:numlattice` is **proved** from them (`Ttc.TtcProb.numlattice`), and so are `eq:almostuniform` (`Ttc.TtcProb.samp_unif`) and the paper's Invariant (`Ttc.TtcProb.theta_lo`/`theta_hi`) |

`L` is the actual normalised lattice count `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)` (`L_eq`).
The output is the algorithm's: `numlattice` is stated over `Ttc.ttcOutput`, so
there is no faithfulness bridge to assume. Inhabited **non-degenerately** by
`Ttc.Box.boxProb` (`Witness/BoxProb`). Running time is out of scope. -/
structure TtcProb (A : Type*) (n : ℕ) where
  /-- The multiplicative accuracy parameter. -/
  ε : ℝ
  /-- The failure probability. -/
  δ : ℝ
  /-- `ε` is positive. -/
  hε0 : 0 < ε
  /-- `ε` is at most one. -/
  hε1 : ε ≤ 1
  /-- `δ` is positive. -/
  hδ0 : 0 < δ
  /-- `δ` is at most one. -/
  hδ1 : δ ≤ 1
  /-- The atoms of the SMT(LRA) formula: each is a linear constraint `A x ≤ b`. -/
  atoms : A → LinAtom n
  /-- The interpretation of atoms as sets of points. -/
  M : A → Set (Space n)
  /-- The interpretation is the one the linear atoms denote — the formula really is
  in the LRA fragment. -/
  M_eq : M = fun a => (atoms a).halfspace
  /-- The Boolean abstraction of the input formula (`alg:ttc` line 15). -/
  φ : BForm A
  /-- **`alg:ttc` line 16**: `F_dnf ← ToDNF(F_bool)`, the circuit-AllSAT call, as a
  function of the formula. A parameter rather than the fixed `Ttc.toDNF`, because
  `thm:runtime`'s `m` is *this* procedure's cube count — see `Ttc.ttcOutput`. -/
  toDNF : BForm A → DNF A
  /-- **The AllSAT call is correct.** Assumed of the external tool; `Ttc.toDNF`
  together with `Ttc.toDNF_isDNFOf` shows the assumption is satisfiable by an
  actual converter, and the witness discharges it that way. -/
  isDNF : IsDNFOf (toDNF φ) φ
  /-- No literal of the DNF is negated, so each `P(cᵢ)` is an intersection of
  *closed* half-spaces. `Ttc.toDNF_isPositive` derives this from a negation-free
  input formula, which is how the witness discharges it — see the README,
  finding 5. -/
  isPositive : DNF.IsPositive (toDNF φ)
  /-- The sample space of the algorithm's randomness. -/
  Ω : Type
  /-- Its σ-algebra. -/
  mΩ : MeasurableSpace Ω
  /-- The law of the algorithm's randomness. -/
  μ : @MeasureTheory.Measure Ω mΩ
  /-- It is a probability measure. -/
  isProb : @MeasureTheory.IsProbabilityMeasure Ω mΩ μ
  /-- The parameter block the run uses. -/
  P : Params
  /-- The run's accuracy parameter is the one the theorem bounds against. -/
  eps_eq : P.ε = ε
  /-- The run's failure probability is the one the theorem bounds against. -/
  delta_eq : P.δ = δ
  /-- The run's dimension is the ambient one. -/
  dim_eq : P.n = n
  /-- `m` bounds the number of polytopes in the decomposition. -/
  cubes_le : (Nat.card {c : Cube A // c ∈ toDNF φ} : ℝ) ≤ P.m
  /-- `r` bounds the total number of facets. -/
  facets_le : (Nat.card (FacetIndex (toDNF φ)) : ℝ) ≤ P.r
  /-- Every facet is a genuine constraint: its normal vector is nonzero. -/
  normal_ne_zero : ∀ j : FacetIndex (toDNF φ),
    0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2
  /-- The oracle bundle **drawn at `ω`** — where all the randomness sits. -/
  O : Ω → Oracles n (Cube A)
  /-- The centre of the ball inscribed in each polytope. -/
  cen : {c : Cube A // c ∈ toDNF φ} → Space n
  /-- `γ̂`, the inscribed-ball radius — what the LP of `alg:prec` returns. The LP is
  not modelled, so this is an input. -/
  gammaHat : ℝ
  /-- `γ̂` is positive. -/
  hgammaHat : 0 < gammaHat
  /-- **`lem:nonconv`'s hypothesis**: each `P(cᵢ)` contains an `ℓ₂`-ball of radius
  `γ̂`, about its own centre `cen i`. -/
  ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val
  /-- Each polytope has finite volume. -/
  volume_ne_top : ∀ i : {c : Cube A // c ∈ toDNF φ}, volume (region M i.val) ≠ ⊤
  /-- `ρ`, the precision `GetPrecision` returns (`alg:ttc` line 17). It fixes the
  lattice `𝕃ⁿ = 10^(-ρ)·ℤⁿ` that `GenerateSamples` draws from. -/
  ρ : ℤ
  /-- `ρ` really is `GetPrecision`'s output for this `γ̂` (`alg:prec` line 91). -/
  rho_eq : ρ = P.precision gammaHat
  /-- **`GenerateSamples`' contract** (`alg:ttc` line 43): the points it returns for
  cube `cᵢ` really are lattice points of `P(cᵢ)`. `Ttc.Oracles` only fixes *how
  many* it returns; that they lie where they should is a property of the external
  sampler, so it is assumed of it here.

  Its **distributional** contract (`eq:sampler`/`eq:almostuniform`: the law is
  within a `(1±ε')` factor of uniform on `P(cᵢ) ∩ 𝕃ⁿ`, pointwise) is no longer
  assumed at all: the field `sampler` below describes the Kannan–Vempala
  construction, and `Ttc.TtcProb.samp_unif` derives the contract from it. -/
  gen_mem : ∀ (ω : Ω) (i : Cube A) (j N : ℕ), i ∈ toDNF φ →
    ∀ s ∈ (O ω).gen i j N ρ, s ∈ region M i ∩ fineLattice n (latticeScale ρ)
  /-- The normalised lattice count `|Sol(F) ∩ 𝕃ⁿ| / 10^(ρ·n)`. -/
  L : ℝ
  /-- `L` really is that count — it is not a free real. -/
  L_eq : L = normalisedCount M φ ρ
  /-- The number of lattice points the coupled family is indexed by.

  **From here on the fields describe the sampler.** `lem:numlattice` is no longer
  assumed: these say *what the randomness is* — the Poisson/thinning family of
  `Coupling/Family` — and the bound is **proved** from them
  (`Ttc.TtcProb.numlattice_union`, hence `Ttc.TtcProb.numlattice`). An assumed
  conclusion about probabilities has been replaced by an assumed description of
  the algorithm's own randomness. -/
  Lidx : ℕ
  /-- An injective enumeration of them. -/
  ptE : Fin Lidx → Space n
  /-- The enumeration really is injective. -/
  ptE_inj : Function.Injective ptE
  /-- **The enumeration lands in `Sol(F) ∩ 𝕃ⁿ`** … -/
  ptE_mem : ∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ)
  /-- … **and hits all of it.** With `ptE_inj` this makes `ptE` a bijection onto
  `Sol(F) ∩ 𝕃ⁿ`, so `Lidx` is the paper's `|Sol(F) ∩ 𝕃ⁿ|` rather than a free
  choice, and the family is indexed by the points the algorithm actually counts. -/
  ptE_onto : ∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x
  /-- Each point's rate at level `0`. -/
  θ : Fin Lidx → ℝ
  /-- The volume estimate the run uses for each cube. -/
  vol : Cube A → ℝ
  /-- `GenerateSamples`' output law on each cube: `sampD i x` is the mass the
  sampler, run on `P(cᵢ)`, puts on the lattice point `x`. -/
  sampD : Cube A → Space n → ℝ
  /-- **`GenerateSamples` is Kannan–Vempala's sampler** — the *construction*, not
  its guarantee. See `Ttc.KV97Sampler` above: the discrete law `sampD` is the
  rejection-normalised randomized rounding of a nearly-uniform continuous draw
  from the inflated dilate `10^ρ · P(cᵢ)`.

  **This field replaces the former `samp_unif`**

  ```
  samp_unif : ∀ i ∈ toDNF φ, ∀ x ∈ region M i ∩ fineLattice n (latticeScale ρ),
    (1 - P.epsPrime) / ((region M i ∩ fineLattice n (latticeScale ρ)).ncard : ℝ)
        ≤ sampD i x ∧
      sampD i x
        ≤ (1 + P.epsPrime) / ((region M i ∩ fineLattice n (latticeScale ρ)).ncard : ℝ)
  ```

  which was `eq:almostuniform` (`sections/related.tex:21`) **assumed** of the
  external sampler. It is now the *theorem* `Ttc.TtcProb.samp_unif`
  (`Ttc/Sampler/Bridge.lean`), with a byte-identical statement, proved from this
  field by `Ttc.almostUniform_of_kv97_density` — i.e. by `Arlib.KV97.theorem2`
  and the `ℤⁿ → 𝕃ⁿ` transport. So the entire Kannan–Vempala development is now
  load-bearing for the headline rather than a parallel justification of it.

  Together with `theta_eq` this also yields the paper's Invariant
  (`analysis.tex:265`), formerly the two fields

  ```
  theta_lo : ∀ s, (1 - P.epsPrime) ^ 2 * (1 - P.eta) / (latticeScale ρ) ^ n ≤ θ s
  theta_hi : ∀ s, θ s ≤ (1 + P.epsPrime) ^ 2 * (1 + P.eta) / (latticeScale ρ) ^ n
  ```

  now `Ttc.TtcProb.theta_lo`/`Ttc.TtcProb.theta_hi`, also with byte-identical
  statements, so nothing downstream changed. -/
  sampler : KV97Sampler A n M (toDNF φ) ρ P.epsPrime sampD
  /-- **How the run accumulates `𝒳`** (`alg:ttc` lines 43–46): each lattice point's
  level-`0` rate is the sampler's mass at that point, times the volume estimate of
  the cube it was drawn from. The cube is existentially quantified because the
  point is drawn from whichever cube of the decomposition contains it.

  This is a description of the algorithm, not a bound on it — the sole
  quantitative input is `Ttc.TtcProb.samp_unif`, itself a theorem. Together they
  yield the paper's Invariant:
  `theta_eq` names the cube, `samp_unif` gives `eq:almostuniform` there,
  `Ttc.TtcProb.volCoins_good` gives `Vol_ED`'s accuracy and
  `Ttc.TtcProb.lattice_cube_lo`/`lattice_cube_hi` give `lem:lattice`, and
  `Ttc.TtcProb.theta_window_cube` telescopes the three. -/
  theta_eq : ∀ s, ∃ i, i ∈ toDNF φ ∧ ptE s ∈ region M i ∧
    θ s = sampD i (ptE s) * vol i
  /-- The coverage test the run uses. -/
  cover : Space n → Cube A → Bool
  /-- Cube membership, on the enumerated points. -/
  memPt : Cube A → Fin Lidx → Bool
  /-- **Cube membership is the geometric one** — `memPt` is not a free predicate.
  Only cubes of `D` are constrained, which is all the run ever reads. -/
  memPt_eq : ∀ i ∈ toDNF φ, ∀ s, memPt i s = true ↔ ptE s ∈ region M i
  /-- Reading a sample point `ω` as a trajectory of the family. -/
  toTraj : Ω → (ℕ → Fin Lidx → ℕ)
  /-- That reading is measurable. -/
  toTraj_meas : @AEMeasurable Ω (ℕ → Fin Lidx → ℕ) _ mΩ toTraj μ
  /-- **The randomness IS the coupled family** — its law is `Ttc.trajLaw`. -/
  law_eq : @MeasureTheory.Measure.map Ω (ℕ → Fin Lidx → ℕ) mΩ _ toTraj μ = trajLaw θ
  /-- **The oracles read that family** (`Ttc.trajOracles`). -/
  oracle_eq : ∀ ω, O ω = trajOracles ptE_inj vol cover memPt (toTraj ω)
  /-- The coverage test agrees with cube membership on the lattice. -/
  cover_eq : ∀ s i, cover (ptE s) i = memPt i s
  /-- **`Vol_ED` is Cousins–Vempala Theorem 1.1** (`vol3_journal.tex:144`), bundled
  as `Ttc.VolumeAlgorithm` (declared at the top of this file; everything *proved*
  about it is in `Ttc/Volume/Bridge.lean`).

  This field and the three below replace the former single field

  ```
  volED_hi : ∀ i ∈ toDNF φ, vol i ≤ (1 + P.epsPrime) * (volume (region M i)).toReal
  ```

  which asserted the bound at *every* sample point — i.e. that `Vol_ED` never
  fails — and so was strictly stronger than what any randomized volume algorithm
  delivers. `Ttc.TtcProb.volED_hi` is now a **theorem** with that exact statement,
  so nothing downstream changed. -/
  volAlg : VolumeAlgorithm n
  /-- The coins the `m` `Vol_ED` calls of `alg:ttc` line 24 consumed.

  A single sample point, not a random variable: `oracle_eq` binds `vol` outside
  the run's `ω`, so the volume estimates are fixed reals throughout the coupling.
  Randomizing them would change `trajOracles` and every lemma below it; the
  probabilistic content is instead carried by `Ttc.TtcProb.volGood_prob`, which
  bounds the measure of the set of coins for which `volCoins_good` holds. -/
  volCoins : volAlg.Ω
  /-- **`vol` is what `Vol_ED` returned.** Each estimate is Theorem 1.1's output
  on the *normalised* polytope — the one that contains the unit ball, as Theorem
  1.1 requires — rescaled by `γ̂ⁿ` (`Ttc.VolumeAlgorithm.of_ball`), at the
  accuracy `ε'` and confidence `δ'` of `alg:ttc` line 18.

  This is the field that stops `vol` being a free function of the right shape: it
  pins it to a named published algorithm. -/
  volED_eq : ∀ (i : Cube A) (hi : i ∈ toDNF φ), vol i =
      gammaHat ^ n * volAlg.est (roundBody (cen ⟨i, hi⟩) gammaHat (region M i))
        P.epsPrime P.deltaPrime volCoins
  /-- **The `m` calls all landed in their good event.** This is the residual
  assumption, and unlike the `volED_hi` it replaces it is an *event*, not a
  posited inequality: `Ttc.TtcProb.volGood_prob` proves it holds with probability
  at least `1 − m·δ' = 1 − δ/4` (`Ttc.Params.vol_failure_eq`), which is exactly
  the share of the failure budget `Ttc.numlattice_failure_le` reserves for the
  volume oracle.

  Two-sided, because that is what Theorem 1.1 gives. The upper half is what
  `Ttc.TtcProb.vol_lt_two_total` consumes; the lower half feeds the Invariant. -/
  volCoins_good : ∀ i ∈ toDNF φ,
      vol i ∈ relErr P.epsPrime (volume (region M i)).toReal
  /-- Every cube of the decomposition carries a positive rate. -/
  vol_pos : ∀ i ∈ toDNF φ, 0 < vol i
  /-- **The instance is big enough for the sketch to be worth running** — the
  paper's own regime. The epoch index `j*` and its window are *not* assumed: they
  follow from this by `Ttc.exists_epoch`, and the first loop's cut-off follows by
  `Ttc.rate_small_of_epoch`. -/
  big : (1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ s


namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- **The DNF the algorithm works with** — line 16's output on the input formula. A
`def`, not a field: the structure carries the *procedure* and the formula, so the
cube list is determined by the input rather than supplied beside it. -/
@[reducible] def D : DNF A := T.toDNF T.φ

/-- **`m`, the number of decomposed polytopes** — the length of the cube list the
main loop folds over. This is `thm:runtime`'s `m`, and `Ttc.TtcProb.cubes_le`
bounds it by the parameter block's `P.m`. -/
def numCubes : ℕ := T.D.length

/-! ### `Vol_ED`'s good event

Two definitions naming what the `m` `Vol_ED` calls of `alg:ttc` line 24 are, so
that `volCoins_good` above has something to be *membership in*. Everything proved
about them — that the former field `volED_hi` follows, and that the event has
probability at least `1 − δ/4` — is in `Ttc/Volume/Bridge.lean`. -/

/-- The `j`-th polytope of the decomposition, with its membership proof — the
`j`-th iteration of `alg:ttc`'s main loop, hence the `j`-th `Vol_ED` call. -/
def cubeAt (j : Fin T.D.length) : {c : Cube A // c ∈ T.toDNF T.φ} :=
  ⟨T.D.get j, List.get_mem _ _⟩

/-- **The good event of the `m` `Vol_ED` calls**, at the parameters `alg:ttc`
lines 18 and 24 use. -/
def volEvent : Set T.volAlg.Ω :=
  volGood T.volAlg T.gammaHat T.P.epsPrime T.P.deltaPrime
    (fun j => T.cen (T.cubeAt j)) (fun j => region T.M (T.D.get j))

end TtcProb

end Ttc
