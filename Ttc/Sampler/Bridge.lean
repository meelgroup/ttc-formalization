/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Lattice.PerCube
import Arlib.Lattice.Basic
import Arlib.Lattice.KV97.Corollary
import Arlib.MarkovChains.Continuous.PointwiseRoute

/-!
# `Sampler/Bridge`: `eq:almostuniform` delivered by Kannan–Vempala

This file is the join between the two halves of the sampling-oracle chain. Both
halves are already proved; nothing here re-proves either.

* **`Arlib` side** — `Arlib.KV97.ratio_bounds_tuned_sharp`
  (`Arlib/Lattice/KV97/Corollary.lean`) says: rejection-sampled randomized
  rounding of an almost-uniform continuous draw lands on each *integer* point of
  a polytope with normalised weight in `[(1−ε)/N, (1+ε)/N]`, `N = Fintype.card ι`
  for an index type `ι` enumerating those points, under `0 < ε ≤ 5/8`.
* **`Ttc` side** — `Ttc.AlmostUniform D S ε` (`Ttc/Sampler/Contract.lean`) is a
  statement about `S.ncard` for `S = P(cᵢ) ∩ 𝕃ⁿ`, and `Ttc.TtcProb.theta_window_cube`
  (`Ttc/Lattice/PerCube.lean`) consumes it to produce the paper's Invariant window.

Three things separate them, and this file closes all three.

## 1. `Fintype.card ι` versus `S.ncard`

`Ttc.card_eq_ncard_of_equiv`: an `Equiv ι ↥S` makes the two numbers equal. The
finiteness and the enumeration are *hypotheses* — they are properties of the
concrete polytope the sampler is run on, not of this bridge.

## 2. `ℤⁿ` versus `𝕃ⁿ`

`Arlib`'s corollary counts points of `ℤⁿ`; the algorithm counts points of
`𝕃ⁿ = 10^(−ρ)·ℤⁿ`. `sections/proof-appendix.tex:181` calls the passage between
them "the isomorphism `φ` of `lem:lattice`" and observes that **neither side of
`eq:almostuniform` changes**, both being normalised by the lattice-point count.

`Ttc.almostUniform_transport` is exactly that observation, proved: from
`Arlib.Lattice.ncard_inter_fineLattice` (the counts agree, because `x ↦ c • x` is
a bijection `S ∩ 𝕃ⁿ ≃ (c • S) ∩ ℤⁿ`) plus
`Arlib.Lattice.smul_mem_intLattice_iff` (the pointwise form), almost-uniformity
on the dilated integer points transports to almost-uniformity on the fine-lattice
points **at the same `ε`**. The transport costs nothing; that is the point.

`Ttc.fineLattice`/`Ttc.latticeScale` (`Ttc/Model/Prelude.lean`) and
`Arlib.Lattice.fineLattice`/`latticeScale` have identical bodies — the `Arlib`
versions were written to match — so the identification is `rfl`
(`Ttc.fineLattice_eq_arlib` and friends) and the `Arlib` transport is reused
verbatim.

## 3. Assembly, and the `ε ≤ 1/2` guard

`Ttc.almostUniform_of_kv97_window` is the weight-level composition at an
arbitrary two-sided window `[(1−a)/V, (1+b)/V]`, via
`Arlib.Rejection.ratio_bounds_of_window`; `Ttc.almostUniform_of_kv97_law` is the
same thing stated over the actual sampler — a **law** `μ` within total variation
`ε/(4·Vol(P'))` of uniform on the inflated dilated polytope, rounded, conditioned
on acceptance.

The window is `a = ε/2`, `b = ε/4`, from the escape mass `E = ε/4`
(`Arlib.KV97.exp_cOf`) and the total-variation shift `θ = ε/4`
(`Arlib.PointwiseRoute.window_of_tvLe`). Recovering the paper's symmetric
`(1 ± ε)/N` then needs `(1−ε)(1+b) ≤ 1−a` — free — and `(1+b) ≤ (1+ε)(1−a)`,
which reduces to **`ε ≤ 1/2`**. `Ttc.TtcProb.epsPrime_le_one_half` proves the
restriction is harmless here: `ε' = ε/12` and `ε ≤ 1`, so `ε' ≤ 1/12`, a factor
of six inside the bar.

The *pointwise* route is still here — `Ttc.almostUniform_of_kv97` and
`Ttc.almostUniform_of_kv97_density`, at the sharper `ε ≤ 5/8` of
`Arlib.KV97.ratio_bounds_tuned_sharp` — but it is **no longer what the headline
goes through**, because its hypothesis is one the real sampler cannot satisfy
(`Arlib.PointwiseRoute.not_pointwiseClose_of_atom`); see §3a. Its tuned window
`[(1−ε/4)(1−E)/V, (1+ε/4)/V]` is *strictly stronger on the low side* than the TV
route's `[(1−(E+θ))/V, (1+θ)/V]` — by `θE`, since `(1−θ)(1−E) = 1−E−θ+θE` — so
the TV route cannot reuse it and goes to `ratio_bounds_of_window` directly.

`Ttc.TtcProb.theta_window_cube_of_kv97_law` is the payoff: the Invariant window
for a cube of the DNF, with `eq:almostuniform` no longer assumed but *derived*
from the Kannan–Vempala hypotheses.

## 4. The sampling oracle, discharged (Part 5)

`Ttc.TtcProb` used to carry the paper's Invariant as the two fields
`theta_lo`/`theta_hi`, and then `eq:almostuniform` as the field `samp_unif`. It
carries neither now. What it carries is `sampD` together with the single field
`sampler : Ttc.KV97Sampler …` — a *description of how `GenerateSamples` is
built*, not of what it achieves — and `theta_eq` (the run's rate at a lattice
point is the sampler's mass there times that cube's volume estimate).

`Ttc.TtcProb.samp_unif` (`eq:almostuniform`), `Ttc.TtcProb.theta_lo` and
`Ttc.TtcProb.theta_hi` are all recovered below as theorems with byte-identical
statements, so every consumer in `Coupling/Transfer` is untouched — which is why
that file now imports this one. Because `samp_unif` is proved through
`Ttc.almostUniform_of_kv97_law`, whose reference window is
`Arlib.KV97.theorem2` at `ε = 0`, `Arlib.KV97.theorem2` is in the transitive
dependency cone of `Ttc.TtcProb.volume_estimate` — and so is the escape estimate
`Ttc.escape_of_mem_body`.

## What is assumed, and what is not

Nothing here is a bound on the sampler's failure probability. What the composed
statements take as hypotheses is a *description* of the sampler and of the
geometry it runs on, none of which this file is in a position to derive:

* `e : ι ≃ ↥((c • S) ∩ ℤⁿ)` — the integer points of the dilated region are
  finitely many and enumerated. (`Arlib.Lattice.finite_inter_intLattice` proves
  finiteness for a *bounded* region; boundedness of `region M i` is not available
  at this generality, so the enumeration is carried.)
* `[Nonempty ι]` — the region contains at least one lattice point. This is the
  same non-degeneracy `Ttc.TtcProb.theta_window_cube` already carries as
  `0 < ncard`; here it is upstream of the count, so it is a `Nonempty`.
* `htv` — the sampler's law is within total variation `ε/(4·Vol(P'))` of uniform
  on `P'`. This is what a mixing bound delivers.
* `hD` — the sampler's output law at a fine-lattice point `x` *is* the normalised
  rounding weight at the dilated point `c • x`. This is the definition of the
  sampler, not a bound on it.

Its third hypothesis, `hesc`, is **not** assumed by `Ttc.KV97Sampler`:
`Ttc.escape_of_mem_body` discharges it from
`Arlib.Lattice.Rounding.setIntegral_prodTent_compl_inflate_le_exp` and the
`dilate_eq` field, for every lattice point of the dilated body.

Everything else — the counts, the transport, the arithmetic — is proved.

## 5. Four audit questions about `Ttc.KV97Sampler`'s fields, settled

Part 3a and the lemmas in Part 5 answer four questions an audit raised about the
hypothesis surface `Ttc.KV97Sampler` presents.

* **Is `contVol` a free gauge?** It *was*, under the density formulation — the
  normaliser cancelled out of `sampD`, which is what the now-deleted
  `Ttc.KV97Sampler.reNormalise` proved. Under the total-variation formulation it
  is **not**: `law_tv`'s tolerance is `ε'/(4·contVol i)`, so moving `contVol`
  changes the hypothesis's strength, and the field `contVol_eq` pins it to
  `Vol(P')`. Part 3a is the record of that change, and
  `Ttc.KV97Sampler.volume_inflated_ne_zero`/`volume_inflated_ne_top` are the two
  side conditions it buys, at no extra assumption.
* **`dilate_eq` was stated as an equality but only `⊆` is used.** True, and
  **fixed**: the field is now that `⊆`, and `Ttc.KV97Sampler.dilate_subset` —
  the name `Ttc.TtcProb.samp_almostUniform_subtype` goes through — is the
  identity on it.
* **`enum`'s finiteness and non-degeneracy are derivable.** True, and **fixed**:
  `idx`, `fintypeIdx`, `nonemptyIdx` and `enum` are all deleted.
  `Ttc.TtcProb.exists_idx_enum` had shown they follow from `ball_subset`,
  `volume_ne_top` and the proved `Ttc.TtcProb.lattice_cube_hi`; `sampD_eq` now
  normalises by a `finsum` over `10^ρ·P(cᵢ) ∩ ℤⁿ`, and Part 5 installs the
  `Fintype`/`Nonempty` from those proofs.
* **`density_int` was a genuine assumption.** It was, and it is **gone** with the
  density it guarded: `prodTent` is bounded and measurable and `contLaw i` is a
  probability measure, so `∫ p, prodTent z p ∂(contLaw i)` needs no admissibility
  hypothesis at all.
-/

namespace Ttc

open MeasureTheory Set Pointwise

/-! ## Part 0: the two libraries' lattices are the same objects

`Ttc/Model/Prelude.lean` and `Arlib/Lattice/Basic.lean` define the lattices
independently, with syntactically identical bodies. Rather than pick one and
refactor the other (which would touch files this file does not own), the three
`rfl`s below record the agreement, and every `Arlib` lemma is then usable on
`Ttc`'s objects by rewriting along them.
-/

/-- `Ttc.intLattice` and `Arlib.Lattice.intLattice` are the same set. -/
theorem intLattice_eq_arlib (n : ℕ) : intLattice n = Arlib.Lattice.intLattice n := rfl

/-- `Ttc.fineLattice` and `Arlib.Lattice.fineLattice` are the same set. -/
theorem fineLattice_eq_arlib (n : ℕ) (c : ℝ) :
    fineLattice n c = Arlib.Lattice.fineLattice n c := rfl

/-- `Ttc.latticeScale` and `Arlib.Lattice.latticeScale` are the same real. -/
theorem latticeScale_eq_arlib (ρ : ℤ) : latticeScale ρ = Arlib.Lattice.latticeScale ρ := rfl

/-! ## Part 1: `Fintype.card` versus `Set.ncard`

`Arlib.KV97.ratio_bounds_tuned_sharp` normalises by `Fintype.card ι`, where `ι`
is whatever type indexes the lattice points; `Ttc.AlmostUniform` normalises by
`S.ncard`. The bridge is a single `Nat.card` hop, and it needs the enumeration as
a hypothesis — there is no way to manufacture one.
-/

/-- **The index bridge.** An enumeration of `S` by a finite type `ι` makes
`Fintype.card ι` and `S.ncard` the same number.

Both are `Nat.card` in disguise: `Nat.card_eq_fintype_card` on the left,
`Nat.card_coe_set_eq` on the right, and `Nat.card` transports along an `Equiv`.
No finiteness of `S` need be assumed separately — it comes from `ι` through
`e`. -/
theorem card_eq_ncard_of_equiv {α ι : Type*} [Fintype ι] {S : Set α} (e : ι ≃ S) :
    Fintype.card ι = S.ncard := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_coe_set_eq]

/-- **`eq:almostuniform` from a pointwise bound along an enumeration.**

If every enumerated point of `S` carries mass within `(1 ± ε)/|ι|`, then `D` is
almost uniform on `S` — the `|ι|` in the denominator becoming `S.ncard` by
`Ttc.card_eq_ncard_of_equiv`. This is the shape `Arlib.KV97`'s conclusions come
in, since they are indexed statements about `w i / ∑ w`. -/
theorem almostUniform_of_ratio_bounds {α ι : Type*} [Fintype ι] {S : Set α}
    (e : ι ≃ S) {D : α → ℝ} {eps : ℝ}
    (h : ∀ k : ι, (1 - eps) / (Fintype.card ι : ℝ) ≤ D (e k) ∧
      D (e k) ≤ (1 + eps) / (Fintype.card ι : ℝ)) :
    AlmostUniform D S eps := by
  intro x hx
  have hcard : ((Fintype.card ι : ℕ) : ℝ) = (S.ncard : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (card_eq_ncard_of_equiv e)
  have hk := h (e.symm ⟨x, hx⟩)
  rw [Equiv.apply_symm_apply, hcard] at hk
  exact hk

/-! ## Part 2: the `ℤⁿ → 𝕃ⁿ` transport

The mathematical content of this file. `Arlib` proves `eq:almostuniform` about
`P ∩ ℤⁿ`; the algorithm needs it about `P(cᵢ) ∩ 𝕃ⁿ`. The dilation `x ↦ c • x`
is a bijection between the two point sets (`Arlib.Lattice.image_smul_inter_fineLattice`,
`Arlib.Lattice.injOn_smul_inter_fineLattice`), hence the counts agree
(`Arlib.Lattice.ncard_inter_fineLattice`), hence *both* sides of
`eq:almostuniform` are unchanged — which is exactly the paper's own remark at
`sections/proof-appendix.tex:181`.
-/

/-- **The counts agree**, stated in `Ttc`'s vocabulary: the fine-lattice points of
`S` are as many as the integer points of the dilate `c • S`.

`Arlib.Lattice.ncard_inter_fineLattice` transported along Part 0. -/
theorem ncard_inter_fineLattice {n : ℕ} {c : ℝ} (hc : 0 < c) (S : Set (Space n)) :
    (S ∩ fineLattice n c).ncard = ((c • S) ∩ intLattice n).ncard := by
  rw [fineLattice_eq_arlib, intLattice_eq_arlib]
  exact Arlib.Lattice.ncard_inter_fineLattice hc S

/-- **Pointwise transport**, in `Ttc`'s vocabulary: `x` is a fine-lattice point of
`S` exactly when `c • x` is an integer point of `c • S`. -/
theorem smul_mem_inter_intLattice_iff {n : ℕ} {c : ℝ} (hc : 0 < c) {S : Set (Space n)}
    {x : Space n} :
    c • x ∈ (c • S) ∩ intLattice n ↔ x ∈ S ∩ fineLattice n c := by
  rw [intLattice_eq_arlib, fineLattice_eq_arlib]
  refine ⟨fun h => ⟨?_, (Arlib.Lattice.smul_mem_intLattice_iff hc).1 h.2⟩,
    fun h => ⟨⟨x, h.1, rfl⟩, (Arlib.Lattice.smul_mem_intLattice_iff hc).2 h.2⟩⟩
  obtain ⟨y, hy, hxy⟩ := h.1
  rwa [smul_right_injective (Space n) hc.ne' hxy] at hy

/-- **THE TRANSPORT** — `eq:almostuniform` moves from `ℤⁿ` to `𝕃ⁿ` for free.

If `D` is almost uniform to accuracy `ε` on the integer points of the dilate
`c • S`, then `x ↦ D (c • x)` is almost uniform to *the same* accuracy `ε` on the
fine-lattice points of `S`.

**Why it is free.** `eq:almostuniform` is a statement about `D x` compared with
`1/|point set|`. The dilation is a bijection of the two point sets, so the two
counts are equal (`Ttc.ncard_inter_fineLattice`) and the right-hand sides of the
two statements are *literally the same real number*; the left-hand sides are
matched by the bijection. Nothing is lost, and no hypothesis beyond `0 < c` is
needed — in particular `S` need not be convex, bounded, or measurable. This is
the paper's own observation at `sections/proof-appendix.tex:181` ("neither side
of `eq:almostuniform` changes, both being normalised by the lattice-point
count"), discharged. -/
theorem almostUniform_transport {n : ℕ} {c : ℝ} (hc : 0 < c) (S : Set (Space n))
    {D : Space n → ℝ} {eps : ℝ}
    (h : AlmostUniform D ((c • S) ∩ intLattice n) eps) :
    AlmostUniform (fun x => D (c • x)) (S ∩ fineLattice n c) eps := by
  intro x hx
  rw [ncard_inter_fineLattice hc S]
  exact h (c • x) ((smul_mem_inter_intLattice_iff hc).2 hx)

/-- The transport at the algorithm's own dilation factor `10^ρ`, so that the
target set is syntactically `P ∩ 𝕃ⁿ` as `Ttc.TtcProb.theta_window_cube` wants
it. -/
theorem almostUniform_transport_latticeScale {n : ℕ} (ρ : ℤ) (S : Set (Space n))
    {D : Space n → ℝ} {eps : ℝ}
    (h : AlmostUniform D ((latticeScale ρ • S) ∩ intLattice n) eps) :
    AlmostUniform (fun x => D (latticeScale ρ • x)) (S ∩ fineLattice n (latticeScale ρ)) eps :=
  almostUniform_transport (latticeScale_pos ρ) S h

/-- Almost-uniformity only sees `D` on `S`, so it may be transported along any
function agreeing with `D` there. This is what lets the composed statements below
conclude about *the sampler's* law `D` rather than about the particular formula
`x ↦ Dint (c • x)` the transport produces. -/
theorem AlmostUniform.congr' {α : Type*} {D D' : α → ℝ} {S : Set α} {eps : ℝ}
    (h : AlmostUniform D S eps) (hEq : ∀ x ∈ S, D' x = D x) : AlmostUniform D' S eps := by
  intro x hx
  rw [hEq x hx]
  exact h x hx

/-! ## Part 3: the composition

Parts 1 and 2 plus `Arlib.KV97.ratio_bounds_tuned_sharp`. Two forms: the
weight-level one, and the one over the actual sampler.
-/

/-- An enumerated nonempty set has positive `ncard` — the non-degeneracy
`Ttc.TtcProb.theta_window_cube` asks for, obtained from `[Nonempty ι]` rather than
assumed separately. -/
theorem ncard_pos_of_equiv {α ι : Type*} [Fintype ι] [Nonempty ι] {S : Set α} (e : ι ≃ S) :
    0 < S.ncard := by
  rw [← card_eq_ncard_of_equiv e]
  exact Fintype.card_pos

/-- Positive count of fine-lattice points, from an enumeration of the integer
points of the dilate. -/
theorem ncard_inter_fineLattice_pos {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {c : ℝ} (hc : 0 < c) {S : Set (Space n)}
    (e : ι ≃ ((c • S) ∩ intLattice n : Set (Space n))) :
    0 < (S ∩ fineLattice n c).ncard := by
  rw [ncard_inter_fineLattice hc S]
  exact ncard_pos_of_equiv e

/-- **`eq:almostuniform` from Kannan–Vempala, weight form.**

Let `ι` enumerate the integer points of the dilate `c • S`, let `w : ι → ℝ` be
unnormalised rounding weights pinned into the tuned Kannan–Vempala window

```
(1 − ε/4)(1 − exp(−(cOf ε)²/2))/V  ≤  w k  ≤  (1 + ε/4)/V,
```

and let the sampler's law `D` on the *fine* lattice read off the normalised
weight at the dilated point (`hDint` and `hD`). Then

```
∀ x ∈ S ∩ 𝕃ⁿ,  (1 − ε)/|S ∩ 𝕃ⁿ|  ≤  D x  ≤  (1 + ε)/|S ∩ 𝕃ⁿ|,
```

which is `Ttc.AlmostUniform D (S ∩ fineLattice n c) ε` on the nose.

Three imported facts do the work and none is re-proved here:
`Arlib.KV97.ratio_bounds_tuned_sharp` (the `(1 ± ε)/N` window over `ι`),
`Ttc.card_eq_ncard_of_equiv` (`Fintype.card ι = ncard`), and
`Ttc.almostUniform_transport` (`ℤⁿ → 𝕃ⁿ`, free).

`ε ≤ 5/8` is inherited from `Arlib.KV97.ratio_bounds_tuned_sharp` and is
**necessary** there — see `Arlib.KV97.tuned_upper_sharp` and `AUDIT-KV97.md` §4g.
`Ttc.TtcProb.epsPrime_le_five_eighths` discharges it for this project. -/
theorem almostUniform_of_kv97 {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {c : ℝ} (hc : 0 < c) {S : Set (Space n)}
    (e : ι ≃ ((c • S) ∩ intLattice n : Set (Space n))) (w : ι → ℝ) {V eps : ℝ}
    (hV : 0 < V) (heps0 : 0 < eps) (heps58 : eps ≤ 5 / 8)
    (hlow : ∀ k, (1 - eps / 4) * (1 - Real.exp (-(Arlib.KV97.cOf eps) ^ 2 / 2)) / V ≤ w k)
    (hhigh : ∀ k, w k ≤ (1 + eps / 4) / V)
    {D Dint : Space n → ℝ}
    (hDint : ∀ k : ι, Dint (e k) = w k / ∑ j, w j)
    (hD : ∀ x ∈ S ∩ fineLattice n c, D x = Dint (c • x)) :
    AlmostUniform D (S ∩ fineLattice n c) eps := by
  refine AlmostUniform.congr' (almostUniform_transport hc S
    (almostUniform_of_ratio_bounds e ?_)) hD
  intro k
  rw [hDint k]
  exact Arlib.KV97.ratio_bounds_tuned_sharp w hV heps0 heps58 hlow hhigh k

/-- **`eq:almostuniform` from Kannan–Vempala, over the sampler itself.**

`Ttc.almostUniform_of_kv97` with the weights replaced by what they actually are:
`w k = ∫_{P'} f p · prodTent (pt k) p dp = Pr[rnd p = pt k]`, the probability that
randomized rounding of a draw from the continuous density `f` on the inflated
dilated polytope `P'` lands on the `k`-th lattice point. The window is then
`Arlib.KV97.theorem2`, and the hypotheses `hf`/`hint`/`hesc` are exactly its own:

* `hf` — `f` is pointwise within `(1 ± ε/4)` of uniform on `P'`;
* `hint` — the integrand is integrable on `P'`;
* `hesc` — the escape mass past `P'` is at most `exp(−(cOf ε)²/2)`, which the
  paper's choice `c = cOf ε = √(2 log(4/ε))` makes exactly `ε/4`
  (`Arlib.KV97.exp_cOf`).

The conclusion is `eq:almostuniform` for the sampler's output law on `S ∩ 𝕃ⁿ`.

This is `Arlib.KV97.cor_linf_tuned` at the *sharp* constant — `cor_linf_tuned`
itself is stated with the honest `1 + 2ε`, valid for all `ε ≤ 1`; here `ε ≤ 5/8`
buys back the paper's symmetric `1 + ε`, as its docstring says it does. -/
theorem almostUniform_of_kv97_density {n : ℕ} {ι J : Type*} [Fintype ι] [Nonempty ι]
    {c : ℝ} (hc : 0 < c) {S : Set (Space n)}
    (e : ι ≃ ((c • S) ∩ intLattice n : Set (Space n)))
    {Amat : J → Space n} {bvec : J → ℝ} {r : ℝ} {f : Space n → ℝ} {V eps : ℝ}
    (hV : 0 < V) (heps0 : 0 < eps) (heps58 : eps ≤ 5 / 8)
    (hf : Arlib.KV97.PointwiseAlmostUniform f
      (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r) V (eps / 4))
    (hint : ∀ k : ι, IntegrableOn
      (fun p => f p * Arlib.Lattice.Rounding.prodTent (e k) p)
      (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r))
    (hesc : ∀ k : ι, ∫ p in (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r)ᶜ,
      Arlib.Lattice.Rounding.prodTent (e k) p ≤ Real.exp (-(Arlib.KV97.cOf eps) ^ 2 / 2))
    {D Dint : Space n → ℝ}
    (hDint : ∀ k : ι, Dint (e k) =
      (∫ p in Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r,
          f p * Arlib.Lattice.Rounding.prodTent (e k) p) /
        ∑ j, ∫ p in Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r,
          f p * Arlib.Lattice.Rounding.prodTent (e j) p)
    (hD : ∀ x ∈ S ∩ fineLattice n c, D x = Dint (c • x)) :
    AlmostUniform D (S ∩ fineLattice n c) eps :=
  almostUniform_of_kv97 hc e
    (fun k => ∫ p in Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r,
      f p * Arlib.Lattice.Rounding.prodTent (e k) p)
    hV heps0 heps58
    (fun k => (Arlib.KV97.theorem2 hV (by linarith) (by linarith) hf (hint k) (hesc k)).1)
    (fun k => (Arlib.KV97.theorem2 hV (by linarith) (by linarith) hf (hint k) (hesc k)).2)
    hDint hD

/-- **`Arlib.KV97.theorem2`'s escape hypothesis, discharged.**

`Ttc.almostUniform_of_kv97_density` asks that the rounding kernel put at most
`exp(−c²/2)` of its mass outside the inflated polytope `P'`. That is *not* an
assumption about the sampler: it is a theorem about the tent kernel, proved in
`Arlib.Lattice.Rounding.setIntegral_prodTent_compl_inflate_le_exp` from the
sub-Gaussian tail of the rounding displacement and a union bound over the `r`
facets. All it needs of the point is that it lies in the polytope `A x ≤ b`
itself — which every enumerated lattice point of the body does, by
`Ttc.KV97Sampler.dilate_eq`.

This is why `Ttc.KV97Sampler` carries no escape-mass field. -/
theorem escape_of_mem_body {n : ℕ} {J : Type*} [Fintype J]
    (Amat : J → Space n) (bvec : J → ℝ) {eps r : ℝ}
    (hr1 : 1 ≤ r) (hr : (Fintype.card J : ℝ) ≤ r)
    {z : Space n} (hz : z ∈ Arlib.Polytope.body Amat bvec) :
    ∫ p in (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r)ᶜ,
        Arlib.Lattice.Rounding.prodTent z p
      ≤ Real.exp (-(Arlib.KV97.cOf eps) ^ 2 / 2) :=
  Arlib.Lattice.Rounding.setIntegral_prodTent_compl_inflate_le_exp Amat bvec hz
    Arlib.KV97.cOf_nonneg hr1 hr

/-- **Non-vacuity of Part 3** (`CLAUDE.md` §11).

`Ttc.almostUniform_of_kv97` quantifies over a bundle of hypotheses; if that
bundle were unsatisfiable the theorem would be worthless. It is satisfiable, and
at the *ideal* sampler it is attained exactly: the constant weight `w = 1/V` sits
inside the tuned Kannan–Vempala window (strictly inside both ends, for every
`0 < ε ≤ 5/8`), its normalisation is exactly `1/|ι|`, and the resulting law on
`S ∩ 𝕃ⁿ` is exactly the uniform one `1/|S ∩ 𝕃ⁿ|` — the `ε = 0` centre of
`eq:almostuniform`, not a boundary case of it.

Note the transport is doing real work even here: the law is uniform over the
*fine*-lattice count, and it is `Ttc.ncard_inter_fineLattice` that says this is
the same number as the integer-point count `Fintype.card ι` the weights were
normalised by. -/
theorem exists_kv97_witness {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {c : ℝ} (hc : 0 < c) {S : Set (Space n)}
    (e : ι ≃ ((c • S) ∩ intLattice n : Set (Space n))) {V eps : ℝ}
    (hV : 0 < V) (heps0 : 0 < eps) (heps58 : eps ≤ 5 / 8) :
    ∃ (w : ι → ℝ) (D Dint : Space n → ℝ),
      (∀ k, (1 - eps / 4) * (1 - Real.exp (-(Arlib.KV97.cOf eps) ^ 2 / 2)) / V ≤ w k) ∧
      (∀ k, w k ≤ (1 + eps / 4) / V) ∧
      (∀ k : ι, Dint (e k) = w k / ∑ j, w j) ∧
      (∀ x ∈ S ∩ fineLattice n c, D x = Dint (c • x)) ∧
      (∀ x ∈ S ∩ fineLattice n c, D x = 1 / ((S ∩ fineLattice n c).ncard : ℝ)) := by
  have hcardN : (Fintype.card ι : ℝ) = ((S ∩ fineLattice n c).ncard : ℝ) := by
    rw [ncard_inter_fineLattice hc S]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (card_eq_ncard_of_equiv e)
  have hcard0 : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨fun _ => 1 / V, fun _ => 1 / ((S ∩ fineLattice n c).ncard : ℝ),
    fun _ => 1 / ((S ∩ fineLattice n c).ncard : ℝ), fun k => ?_, fun k => by
      rw [div_le_div_iff_of_pos_right hV]; linarith, fun k => ?_,
    fun x _ => rfl, fun x _ => rfl⟩
  · have hexp : 0 < Real.exp (-(Arlib.KV97.cOf eps) ^ 2 / 2) := Real.exp_pos _
    have : (1 - eps / 4) * (1 - Real.exp (-(Arlib.KV97.cOf eps) ^ 2 / 2)) ≤ 1 := by
      nlinarith
    rw [div_le_div_iff_of_pos_right hV]
    linarith
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcardN]
    field_simp

/-! ## Part 3': the total-variation route, which is the one the sampler can walk

Everything above takes a *density* that is pointwise almost uniform on `P'`.
`Arlib.PointwiseRoute.not_pointwiseClose_of_atom` shows no ball-walk law started
at a point is ever pointwise close to uniform — the holding atom
`(1 − ℓ(x))·δ_x` survives forever, and one atom defeats pointwise closeness for
*every* `ε`, `⊤` included. So `Ttc.KV97Sampler` carries a **law** and a
**total-variation** bound instead, and this section is the passage from that
hypothesis to `eq:almostuniform`.

Three steps, each a named lemma:

1. `Ttc.uniformOn_prodTent_window` — the *reference* window. Under the exactly
   uniform law on `P'`, `Pr[rnd p = z]` lies in `[(1−E)/V, 1/V]`. This is
   `Arlib.KV97.theorem2` **at `ε = 0`**, which is why Kannan–Vempala's Theorem 2
   remains load-bearing on this route rather than being replaced by it.
2. `Ttc.prodTent_window_of_tvLe` — the *transfer*. A total-variation bound of
   `θ/V` widens that window to `[(1−(E+θ))/V, (1+θ)/V]`
   (`Arlib.PointwiseRoute.window_of_tvLe`: an additive error `ε` is a relative
   error `ε·V`, so the tolerance must carry the `1/V`).
3. `Ttc.almostUniform_of_kv97_window` — the *normalisation*. Rejection turns a
   two-sided window into a two-sided ratio bound, by
   `Arlib.Rejection.ratio_bounds_of_window`.

`Ttc.almostUniform_of_kv97_law` composes the three at the tuned values
`E = θ = ε/4`, i.e. `a = ε/2`, `b = ε/4`.
-/

/-- **Window to ratio, at an arbitrary two-sided window.**

`Ttc.almostUniform_of_kv97` is this lemma's tuned cousin, specialised through
`Arlib.KV97.ratio_bounds_tuned_sharp`. The TV route cannot use that
specialisation — its window `[(1−(E+θ))/V, (1+θ)/V]` is weaker on the low side
than the pointwise route's `[(1−ε/4)(1−E)/V, (1+ε/4)/V]` by exactly `θE` — so it
goes to `Arlib.Rejection.ratio_bounds_of_window` directly and carries the two
arithmetic side conditions explicitly.

The side conditions `hlo'`, `hhi'` are precisely what it takes for the ratio
window `[(1−a)/((1+b)N), (1+b)/((1−a)N)]` that rejection produces to sit inside
`eq:almostuniform`'s `[(1−ε)/N, (1+ε)/N]`. -/
theorem almostUniform_of_kv97_window {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {c : ℝ} (hc : 0 < c) {S : Set (Space n)}
    (e : ι ≃ ((c • S) ∩ intLattice n : Set (Space n))) (w : ι → ℝ) {V a b eps : ℝ}
    (hV : 0 < V) (ha : a < 1)
    (hlow : ∀ k, (1 - a) / V ≤ w k) (hhigh : ∀ k, w k ≤ (1 + b) / V)
    (hlo' : (1 - eps) * (1 + b) ≤ 1 - a) (hhi' : 1 + b ≤ (1 + eps) * (1 - a))
    {D Dint : Space n → ℝ}
    (hDint : ∀ k : ι, Dint (e k) = w k / ∑ j, w j)
    (hD : ∀ x ∈ S ∩ fineLattice n c, D x = Dint (c • x)) :
    AlmostUniform D (S ∩ fineLattice n c) eps := by
  have ha' : (0 : ℝ) < 1 - a := by linarith
  have hb' : (0 : ℝ) < 1 + b := by
    obtain ⟨k⟩ := ‹Nonempty ι›
    have h1 : (1 - a) / V ≤ (1 + b) / V := le_trans (hlow k) (hhigh k)
    nlinarith [(div_le_div_iff_of_pos_right hV).1 h1]
  have hN : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  refine AlmostUniform.congr' (almostUniform_transport hc S
    (almostUniform_of_ratio_bounds e ?_)) hD
  intro k
  obtain ⟨h1, h2⟩ := Arlib.Rejection.ratio_bounds_of_window w hV ha hlow hhigh k
  rw [hDint k]
  refine ⟨le_trans ?_ h1, le_trans h2 ?_⟩
  · rw [← div_div]
    gcongr
    rw [le_div_iff₀ hb']
    exact hlo'
  · rw [← div_div]
    gcongr
    rw [div_le_iff₀ ha']
    exact hhi'

/-- **The reference window: `Arlib.KV97.theorem2` at `ε = 0`.**

Under the *exactly* uniform law on the inflated polytope `P'`, the rounding
kernel's average lies in `[(1−E)/V, 1/V]`, `E` bounding the escape mass. The
uniform law does have a density — the constant `1/V` — so Kannan–Vempala's
Theorem 2 applies to it verbatim at accuracy `0`; `Arlib.integral_uniformOn_real`
is the identification of the measure-form integral with the density-form one.

This is the step that keeps `Arlib.KV97.theorem2` load-bearing on the
total-variation route: the TV hypothesis is a *perturbation* of the uniform law,
and the unperturbed statement is Theorem 2. -/
theorem uniformOn_prodTent_window {n : ℕ} {J : Type*}
    {Amat : J → Space n} {bvec : J → ℝ} {cc r V E : ℝ} {z : Space n}
    (hVS : (volume (Arlib.KV97.inflated Amat bvec cc r)).toReal = V) (hV : 0 < V)
    (hesc : ∫ p in (Arlib.KV97.inflated Amat bvec cc r)ᶜ,
      Arlib.Lattice.Rounding.prodTent z p ≤ E) :
    (1 - E) / V ≤ ∫ p, Arlib.Lattice.Rounding.prodTent z p
        ∂(Arlib.uniformOn volume (Arlib.KV97.inflated Amat bvec cc r)) ∧
      ∫ p, Arlib.Lattice.Rounding.prodTent z p
        ∂(Arlib.uniformOn volume (Arlib.KV97.inflated Amat bvec cc r)) ≤ (1 + 0) / V := by
  have hval : ∫ p, Arlib.Lattice.Rounding.prodTent z p
      ∂(Arlib.uniformOn volume (Arlib.KV97.inflated Amat bvec cc r))
      = ∫ p in Arlib.KV97.inflated Amat bvec cc r,
          (1 / V) * Arlib.Lattice.Rounding.prodTent z p := by
    rw [Arlib.integral_uniformOn_real, hVS, one_div, integral_const_mul]
  obtain ⟨h1, h2⟩ := Arlib.KV97.theorem2 (A := Amat) (b := bvec) (c := cc) (r := r)
    (f := fun _ => 1 / V) (x := z) (E := E) hV (by norm_num) (by norm_num)
    (Arlib.KV97.PointwiseAlmostUniform.uniform _ hV le_rfl)
    ((Arlib.Lattice.Rounding.integrableOn_prodTent z _).const_mul _) hesc
  rw [hval]
  refine ⟨?_, h2⟩
  calc (1 - E) / V = (1 - 0) * (1 - E) / V := by ring
    _ ≤ _ := h1

/-- **The transfer: a total-variation bound widens the reference window by `θ`.**

`Arlib.PointwiseRoute.window_of_tvLe` applied to the rounding kernel, which is
measurable and `[0,1]`-valued. The tolerance is `θ/V`, and *that is the point*:
an additive error `ε` is a relative error `ε·V`, so a sampler asked for
total-variation `θ/Vol(P')` delivers a *relative* `θ`
(`AUDIT-KV97.md` §4b, boxed correction).

`Vol(P') ∉ {0, ∞}` appears because the uniform law is a probability measure only
there; `Ttc.KV97Sampler` supplies both from `contVol_pos` and `contVol_eq`. -/
theorem prodTent_window_of_tvLe {n : ℕ} {J : Type*}
    {Amat : J → Space n} {bvec : J → ℝ} {cc r V E theta : ℝ} {z : Space n}
    {mu : Measure (Space n)} [IsProbabilityMeasure mu]
    (h0 : volume (Arlib.KV97.inflated Amat bvec cc r) ≠ 0)
    (htop : volume (Arlib.KV97.inflated Amat bvec cc r) ≠ ⊤)
    (hVS : (volume (Arlib.KV97.inflated Amat bvec cc r)).toReal = V) (hV : 0 < V)
    (htv : Arlib.TVLe mu (Arlib.uniformOn volume (Arlib.KV97.inflated Amat bvec cc r))
      (ENNReal.ofReal (theta / V))) (htheta : 0 ≤ theta)
    (hesc : ∫ p in (Arlib.KV97.inflated Amat bvec cc r)ᶜ,
      Arlib.Lattice.Rounding.prodTent z p ≤ E) :
    (1 - (E + theta)) / V ≤ ∫ p, Arlib.Lattice.Rounding.prodTent z p ∂mu ∧
      ∫ p, Arlib.Lattice.Rounding.prodTent z p ∂mu ≤ (1 + theta) / V := by
  haveI : IsProbabilityMeasure
      (Arlib.uniformOn volume (Arlib.KV97.inflated Amat bvec cc r)) :=
    Arlib.isProbabilityMeasure_uniformOn volume h0 htop
  obtain ⟨r1, r2⟩ := uniformOn_prodTent_window hVS hV hesc
  have hεV : (ENNReal.ofReal (theta / V)).toReal * V ≤ theta := by
    rw [ENNReal.toReal_ofReal (div_nonneg htheta hV.le), div_mul_cancel₀ _ hV.ne']
  obtain ⟨h1, h2⟩ := Arlib.PointwiseRoute.window_of_tvLe htv ENNReal.ofReal_ne_top
    (Arlib.Lattice.Rounding.measurable_prodTent z)
    (fun p => Arlib.Lattice.Rounding.prodTent_nonneg z p)
    (fun p => Arlib.PointwiseRoute.prodTent_le_one z p) hV hεV r1 r2
  exact ⟨h1, by simpa using h2⟩

/-- **`eq:almostuniform` from Kannan–Vempala, over the sampler's *law*.**

The total-variation replacement for `Ttc.almostUniform_of_kv97_density`. The
weights are `w k = ∫ prodTent (pt k) p ∂μ = Pr[rnd p = pt k]`, computed against
the sampler's law `μ` rather than a density — the measure form is the primitive
one, and it is the only one a chain with atoms can satisfy.

The hypotheses are exactly `Ttc.KV97Sampler`'s fields plus what
`Ttc.escape_of_mem_body` discharges:

* `htv` — `μ` is within total variation `ε/(4·V)` of uniform on `P'` (`law_tv`);
* `h0`/`htop`/`hVS` — `V = Vol(P') ∈ (0, ∞)` (`contVol_pos` + `contVol_eq`);
* `hesc` — the escape mass past `P'` is at most `exp(−(cOf ε)²/2) = ε/4`
  (`Arlib.KV97.exp_cOf`), a *theorem* about the tent kernel, not a field.

The resulting window is `a = ε/2`, `b = ε/4`, and recovering the paper's
symmetric `(1 ± ε)/N` from it needs `ε ≤ 1/2` — see
`Ttc.TtcProb.epsPrime_le_one_half`. -/
theorem almostUniform_of_kv97_law {n : ℕ} {ι J : Type*} [Fintype ι] [Nonempty ι]
    {c : ℝ} (hc : 0 < c) {S : Set (Space n)}
    (e : ι ≃ ((c • S) ∩ intLattice n : Set (Space n)))
    {Amat : J → Space n} {bvec : J → ℝ} {r : ℝ}
    {mu : Measure (Space n)} [IsProbabilityMeasure mu] {V eps : ℝ}
    (hV : 0 < V) (heps0 : 0 < eps) (heps12 : eps ≤ 1 / 2)
    (h0 : volume (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r) ≠ 0)
    (htop : volume (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r) ≠ ⊤)
    (hVS : (volume (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r)).toReal = V)
    (htv : Arlib.TVLe mu
      (Arlib.uniformOn volume (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r))
      (ENNReal.ofReal (eps / (4 * V))))
    (hesc : ∀ k : ι, ∫ p in (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r)ᶜ,
      Arlib.Lattice.Rounding.prodTent (e k) p ≤ Real.exp (-(Arlib.KV97.cOf eps) ^ 2 / 2))
    {D Dint : Space n → ℝ}
    (hDint : ∀ k : ι, Dint (e k) =
      (∫ p, Arlib.Lattice.Rounding.prodTent (e k) p ∂mu) /
        ∑ j, ∫ p, Arlib.Lattice.Rounding.prodTent (e j) p ∂mu)
    (hD : ∀ x ∈ S ∩ fineLattice n c, D x = Dint (c • x)) :
    AlmostUniform D (S ∩ fineLattice n c) eps := by
  have hE : Real.exp (-(Arlib.KV97.cOf eps) ^ 2 / 2) = eps / 4 :=
    Arlib.KV97.exp_cOf heps0 (by linarith)
  have hesc' : ∀ k : ι, ∫ p in (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r)ᶜ,
      Arlib.Lattice.Rounding.prodTent (e k) p ≤ eps / 4 := by
    intro k; rw [← hE]; exact hesc k
  have htv' : Arlib.TVLe mu
      (Arlib.uniformOn volume (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf eps) r))
      (ENNReal.ofReal (eps / 4 / V)) := by
    rwa [← div_div] at htv
  have hw := fun k : ι =>
    prodTent_window_of_tvLe (theta := eps / 4) (E := eps / 4) h0 htop hVS hV htv'
      (by linarith) (hesc' k)
  exact almostUniform_of_kv97_window (a := eps / 4 + eps / 4) (b := eps / 4) hc e
    (fun k => ∫ p, Arlib.Lattice.Rounding.prodTent (e k) p ∂mu) hV (by linarith)
    (fun k => (hw k).1) (fun k => (hw k).2) (by nlinarith) (by nlinarith) hDint hD

/-! ## Part 3a: `contVol` is **determined**, not a gauge

Under the density formulation `Ttc.KV97Sampler.contVol` was unconstrained, and
that cost nothing: `sampD` is a ratio of two integrals linear in the density, so
a positive scalar cancelled between numerator and denominator, and the deleted
`Ttc.KV97Sampler.reNormalise` moved `contVol` anywhere while leaving `sampD`
pointwise fixed. The normaliser was a **gauge**.

**That is a fact about the density formulation, and it does not survive the
swap.** `law_tv`'s tolerance is `ε'/(4·contVol i)`: shrinking `contVol` strictly
strengthens the hypothesis and enlarging it strictly weakens it, so there is no
rescaling of the law that compensates. `contVol` is now pinned by the field
`contVol_eq`, and `reNormalise`, its four `@[simp]` projections, and
`Ttc.exists_contVol_eq_volume_inflated` are gone with the question they answered.

What the pinning *buys* is the two side conditions the total-variation route
needs — `Vol(P') ≠ 0` and `Vol(P') ≠ ∞`, without which the uniform reference law
is not a probability measure. Both come out of `contVol_pos` and `contVol_eq`
together, because `0 < x.toReal` already forces `x ∉ {0, ∞}`. So the swap adds no
assumption on this axis; it converts a free parameter into a determined one and
gets the guards for free.
-/

namespace KV97Sampler

variable {A : Type*} {n : ℕ} {M : A → Set (Space n)} {D : DNF A} {ρ : ℤ}
  {epsPrime : ℝ} {sampD : Cube A → Space n → ℝ}

/-- **The inclusion the escape estimate consumes.**

`Ttc.TtcProb.samp_almostUniform_subtype` discharges `Arlib.KV97.theorem2`'s
escape hypothesis through `Ttc.escape_of_mem_body`, which needs only that each
enumerated lattice point of the *dilate* lies in the *body*, i.e. the inclusion
`10^ρ·P(cᵢ) ⊆ body(A,b)`. This lemma is the name the proof routes through, so
the dependence is visible rather than latent.

`Ttc.KV97Sampler.dilate_eq` used to be the *equality* `body(A,b) = 10^ρ·P(cᵢ)`
and this lemma its weaker half; the field has since been weakened to exactly
this inclusion, so the lemma is now the identity on it. -/
theorem dilate_subset (S : KV97Sampler A n M D ρ epsPrime sampD)
    (i : {c : Cube A // c ∈ D}) :
    latticeScale ρ • region M i.val ⊆ Arlib.Polytope.body (S.Amat i) (S.bvec i) :=
  S.dilate_eq i

/-- **`Vol(P') ≠ 0`** — one of the two guards the total-variation route needs, and
it costs nothing: `contVol_pos` and `contVol_eq` say `0 < (Vol P').toReal`, and
`ENNReal.toReal` sends `0` to `0`. -/
theorem volume_inflated_ne_zero (S : KV97Sampler A n M D ρ epsPrime sampD)
    (i : {c : Cube A // c ∈ D}) :
    volume (Arlib.KV97.inflated (S.Amat i) (S.bvec i)
      (Arlib.KV97.cOf epsPrime) S.facetBound) ≠ 0 := by
  have h : 0 < (volume (Arlib.KV97.inflated (S.Amat i) (S.bvec i)
      (Arlib.KV97.cOf epsPrime) S.facetBound)).toReal := by
    rw [← S.contVol_eq i]; exact S.contVol_pos i
  exact (ENNReal.toReal_pos_iff.1 h).1.ne'

/-- **`Vol(P') ≠ ∞`** — the other guard, from the same two fields: `ENNReal.toReal`
sends `∞` to `0` as well. -/
theorem volume_inflated_ne_top (S : KV97Sampler A n M D ρ epsPrime sampD)
    (i : {c : Cube A // c ∈ D}) :
    volume (Arlib.KV97.inflated (S.Amat i) (S.bvec i)
      (Arlib.KV97.cOf epsPrime) S.facetBound) ≠ ⊤ := by
  have h : 0 < (volume (Arlib.KV97.inflated (S.Amat i) (S.bvec i)
      (Arlib.KV97.cOf epsPrime) S.facetBound)).toReal := by
    rw [← S.contVol_eq i]; exact S.contVol_pos i
  exact (ENNReal.toReal_pos_iff.1 h).2.ne

end KV97Sampler

/-! ## Part 3b: the rounding kernel is `[0,1]`-valued

`Arlib.TVLe.integral_le` transfers *observables* bounded between `0` and `1`, so
the total-variation route needs `prodTent ∈ [0,1]`. `Arlib.Lattice.Rounding`
records only the lower half; these two lemmas are the upper one.

The former contents of this section — `Ttc.integrableOn_density_mul_prodTent`,
which isolated exactly what the deleted `density_int` field assumed over and
above `density_au` — are gone with both fields. Under `contLaw` there is nothing
left to assume: `prodTent` is bounded and measurable and the law is a probability
measure, so the integral always exists.
-/

/-- The tent density never exceeds `1`. -/
theorem tent_le_one (u : ℝ) : Arlib.Lattice.Rounding.tent u ≤ 1 :=
  max_le (by linarith [abs_nonneg u]) zero_le_one

/-- Hence neither does the product kernel: `prodTent x p ∈ [0,1]`, so it is the
conditional probability it is named after. -/
theorem prodTent_le_one {n : ℕ} (x p : Space n) :
    Arlib.Lattice.Rounding.prodTent x p ≤ 1 :=
  Finset.prod_le_one (fun _ _ => Arlib.Lattice.Rounding.tent_nonneg _)
    (fun _ _ => tent_le_one _)

/-! ## Part 4: the payoff

`Ttc.TtcProb.theta_window_cube` (`Ttc/Lattice/PerCube.lean`) previously required
`eq:almostuniform` as a hypothesis. It no longer has to: Part 3 produces it from
the Kannan–Vempala description of the sampler.
-/

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- `ε' = ε/12 > 0`, from `0 < ε`. The *strict* form; `Ttc/Sampler/Contract.lean`
carries only `0 ≤ ε'`, and `Arlib.KV97.ratio_bounds_tuned_sharp` needs strict
positivity (it takes logarithms of `4/ε'`).

**Primed** because `Ttc/Coupling/Transfer.lean` already declares an
identically-stated `Ttc.TtcProb.epsPrime_pos`, and that file now *imports* this
one (it consumes `Ttc.TtcProb.theta_lo`/`theta_hi` below), so the two names would
collide. The convention matches `Ttc.TtcProb.epsPrime_le_one'`, which Transfer
primes for the same reason against `Ttc/Sampler/Contract.lean`'s
`epsPrime_le_one`. -/
theorem epsPrime_pos' : 0 < T.P.epsPrime := by
  have h := T.hε0
  rw [Params.epsPrime, T.eps_eq]
  linarith

/-- **§4g's restriction is harmless here.** `Arlib.KV97.ratio_bounds_tuned_sharp`
carries `ε ≤ 5/8`, and that restriction is real: the paper's `(1 ± ε)` claim is
*false* for `ε > (7 − √33)/2 ≈ 0.6277` (`Arlib.KV97.tuned_upper_sharp`,
`AUDIT-KV97.md` §4g). This lemma is why it costs this project nothing.

The sampler is run at `ε' = ε/12`, and the problem setting carries `ε ≤ 1`
(`Ttc.TtcProb.hε1`), so `ε' ≤ 1/12 ≈ 0.083` — a factor of `7.5` inside the
admissible range, and a factor of `7.5` inside the true threshold too. There is
no parameter regime of `TTC` in which the correction bites. -/
theorem epsPrime_le_five_eighths : T.P.epsPrime ≤ 5 / 8 := by
  have h := T.hε1
  have h0 := T.hε0
  rw [Params.epsPrime, T.eps_eq]
  linarith

/-- The sharper statement `ε' ≤ 1/12`, recorded because it is the honest margin:
`5/8` is where `Arlib.KV97` stops, `1/12` is where this project actually sits. -/
theorem epsPrime_le_one_twelfth : T.P.epsPrime ≤ 1 / 12 := by
  have h := T.hε1
  rw [Params.epsPrime, T.eps_eq]
  linarith

/-- **The guard the total-variation route carries, and why it is harmless here.**

`Ttc.almostUniform_of_kv97_window` recovers `eq:almostuniform`'s symmetric
`(1 ± ε)/N` from the rejection window `[(1−a)/((1+b)N), (1+b)/((1−a)N)]` only if
`1 + b ≤ (1 + ε)(1 − a)`. At the tuned values `a = ε/2`, `b = ε/4` that reduces
to exactly `ε ≤ 1/2` — a *different* bar from the `ε ≤ 5/8` of
`Arlib.KV97.ratio_bounds_tuned_sharp`, which the pointwise route used, and one
that no existing lemma supplied.

It costs this project nothing either: the sampler is run at `ε' = ε/12` and the
problem setting carries `ε ≤ 1` (`Ttc.TtcProb.hε1`), so `ε' ≤ 1/12` — a factor of
six inside the bar. `Ttc.TtcProb.epsPrime_le_one_twelfth` is the honest
margin. -/
theorem epsPrime_le_one_half : T.P.epsPrime ≤ 1 / 2 := by
  have h := T.epsPrime_le_one_twelfth
  linarith

/-- **THE PAYOFF, pointwise route.** `analysis.tex:271`'s Invariant window for a
cube of the DNF, with `eq:almostuniform` **derived** rather than assumed.

This is the *density* form, kept because the arithmetic is sharper (`ε ≤ 5/8`
against the total-variation route's `ε ≤ 1/2`) and because it records what a
pointwise guarantee would buy. It is **not** what the headline goes through —
`Ttc.TtcProb.theta_window_cube_of_kv97_law` is, because `Ttc.KV97Sampler` now
carries a law and a total-variation bound rather than a density.

Compare `Ttc.TtcProb.theta_window_cube`, which takes `AlmostUniform D … ε'` as a
hypothesis. Here that hypothesis is replaced by the Kannan–Vempala description of
how the sampler is realised — a pointwise-almost-uniform continuous density `f`
on the inflated dilated polytope, randomized rounding, rejection — and
`eq:almostuniform` is produced by `Ttc.almostUniform_of_kv97_density`. The
`ε' ≤ 5/8` side condition of `Arlib.KV97.ratio_bounds_tuned_sharp` is discharged
by `Ttc.TtcProb.epsPrime_le_five_eighths`, and the non-degeneracy `0 < ncard` is
discharged by `Ttc.ncard_inter_fineLattice_pos` from `[Nonempty ι]`; neither
appears in the statement.

The conclusion is literally `Ttc.TtcProb.theta_lo`/`theta_hi` with
`θ x := D x · vol i`, exactly as in `Ttc.TtcProb.theta_window_cube`. Those two are
now theorems of Part 5 below rather than `Ttc.TtcProb` fields. -/
theorem theta_window_cube_of_kv97 {ι J : Type*} [Fintype ι] [Nonempty ι]
    {i : Cube A} (hi : i ∈ T.toDNF T.φ)
    (e : ι ≃ ((latticeScale T.ρ • region T.M i) ∩ intLattice n : Set (Space n)))
    {Amat : J → Space n} {bvec : J → ℝ} {r : ℝ} {f : Space n → ℝ} {V : ℝ}
    (hV : 0 < V)
    (hf : Arlib.KV97.PointwiseAlmostUniform f
      (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf T.P.epsPrime) r) V (T.P.epsPrime / 4))
    (hint : ∀ k : ι, IntegrableOn
      (fun p => f p * Arlib.Lattice.Rounding.prodTent (e k) p)
      (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf T.P.epsPrime) r))
    (hesc : ∀ k : ι,
      ∫ p in (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf T.P.epsPrime) r)ᶜ,
        Arlib.Lattice.Rounding.prodTent (e k) p
          ≤ Real.exp (-(Arlib.KV97.cOf T.P.epsPrime) ^ 2 / 2))
    {D Dint : Space n → ℝ}
    (hDint : ∀ k : ι, Dint (e k) =
      (∫ p in Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf T.P.epsPrime) r,
          f p * Arlib.Lattice.Rounding.prodTent (e k) p) /
        ∑ j, ∫ p in Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf T.P.epsPrime) r,
          f p * Arlib.Lattice.Rounding.prodTent (e j) p)
    (hD : ∀ x ∈ region T.M i ∩ fineLattice n (latticeScale T.ρ),
      D x = Dint (latticeScale T.ρ • x))
    {x : Space n} (hx : x ∈ region T.M i ∩ fineLattice n (latticeScale T.ρ)) :
    (1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) / (latticeScale T.ρ) ^ n ≤ D x * T.vol i ∧
      D x * T.vol i
        ≤ (1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) / (latticeScale T.ρ) ^ n :=
  T.theta_window_cube hi (ncard_inter_fineLattice_pos (latticeScale_pos T.ρ) e)
    (almostUniform_of_kv97_density (latticeScale_pos T.ρ) e hV T.epsPrime_pos'
      T.epsPrime_le_five_eighths hf hint hesc hDint hD)
    hx

/-- **THE PAYOFF.** The same Invariant window, from the hypothesis the sampler can
actually meet: a **law** `μ` within total variation `ε'/(4·Vol(P'))` of uniform on
the inflated dilated polytope.

`eq:almostuniform` is produced by `Ttc.almostUniform_of_kv97_law`, whose reference
window is `Arlib.KV97.theorem2` at `ε = 0`. The `ε' ≤ 1/2` side condition is
discharged by `Ttc.TtcProb.epsPrime_le_one_half` and the non-degeneracy
`0 < ncard` by `Ttc.ncard_inter_fineLattice_pos` from `[Nonempty ι]`; neither
appears in the statement, which is byte-identical to the pointwise route's. -/
theorem theta_window_cube_of_kv97_law {ι J : Type*} [Fintype ι] [Nonempty ι]
    {i : Cube A} (hi : i ∈ T.toDNF T.φ)
    (e : ι ≃ ((latticeScale T.ρ • region T.M i) ∩ intLattice n : Set (Space n)))
    {Amat : J → Space n} {bvec : J → ℝ} {r : ℝ}
    {mu : Measure (Space n)} [IsProbabilityMeasure mu] {V : ℝ} (hV : 0 < V)
    (h0 : volume (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf T.P.epsPrime) r) ≠ 0)
    (htop : volume (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf T.P.epsPrime) r) ≠ ⊤)
    (hVS : (volume (Arlib.KV97.inflated Amat bvec
      (Arlib.KV97.cOf T.P.epsPrime) r)).toReal = V)
    (htv : Arlib.TVLe mu
      (Arlib.uniformOn volume
        (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf T.P.epsPrime) r))
      (ENNReal.ofReal (T.P.epsPrime / (4 * V))))
    (hesc : ∀ k : ι,
      ∫ p in (Arlib.KV97.inflated Amat bvec (Arlib.KV97.cOf T.P.epsPrime) r)ᶜ,
        Arlib.Lattice.Rounding.prodTent (e k) p
          ≤ Real.exp (-(Arlib.KV97.cOf T.P.epsPrime) ^ 2 / 2))
    {D Dint : Space n → ℝ}
    (hDint : ∀ k : ι, Dint (e k) =
      (∫ p, Arlib.Lattice.Rounding.prodTent (e k) p ∂mu) /
        ∑ j, ∫ p, Arlib.Lattice.Rounding.prodTent (e j) p ∂mu)
    (hD : ∀ x ∈ region T.M i ∩ fineLattice n (latticeScale T.ρ),
      D x = Dint (latticeScale T.ρ • x))
    {x : Space n} (hx : x ∈ region T.M i ∩ fineLattice n (latticeScale T.ρ)) :
    (1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) / (latticeScale T.ρ) ^ n ≤ D x * T.vol i ∧
      D x * T.vol i
        ≤ (1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) / (latticeScale T.ρ) ^ n :=
  T.theta_window_cube hi (ncard_inter_fineLattice_pos (latticeScale_pos T.ρ) e)
    (almostUniform_of_kv97_law (latticeScale_pos T.ρ) e hV T.epsPrime_pos'
      T.epsPrime_le_one_half h0 htop hVS htv hesc hDint hD)
    hx

/-! ## Part 5: the sampling oracle, discharged

`Ttc.TtcProb` used to **assume** the paper's Invariant, as the two fields

```
theta_lo : ∀ s, (1 - P.epsPrime) ^ 2 * (1 - P.eta) / (latticeScale ρ) ^ n ≤ θ s
theta_hi : ∀ s, θ s ≤ (1 + P.epsPrime) ^ 2 * (1 + P.eta) / (latticeScale ρ) ^ n
```

Those fields are gone, and so is the field `samp_unif` that first replaced them.
What replaces *that* in `Model/ProblemSetting` is `sampD`/`sampler` — the
Kannan–Vempala **construction** of `GenerateSamples` (`Ttc.KV97Sampler`) — and
`theta_eq`, which says how the run turns the resulting law into a rate
(`θ s = sampD i (ptE s) · vol i`). The first is a description of the external
sampler's mechanism; the second is a description of `alg:ttc`'s own bookkeeping.
Neither says where the rates land, and neither asserts `eq:almostuniform`: that
is now proved.

The window is recovered below with **byte-identical statements**, so every
consumer (`Ttc.TtcProb.theta_nonneg`, `sum_theta_lo`, `sum_theta_hi` in
`Coupling/Transfer`) is untouched. The proof is `Ttc.TtcProb.theta_window_cube`
(`Lattice/PerCube`), which already assembles `eq:almostuniform` with `Vol_ED`'s
two-sided accuracy (`Ttc.TtcProb.volED_lo`/`volED_hi`, proved) and the per-cube
`lem:lattice` (`Ttc.TtcProb.lattice_cube_lo`/`lattice_cube_hi`, proved).

The one side condition `theta_window_cube` carries, `0 < |P(cᵢ) ∩ 𝕃ⁿ|`, is
**not** a new assumption either: `Ttc.TtcProb.lattice_finite_cube` derives
finiteness from `ptE_onto` (the enumeration is onto `Sol(F) ∩ 𝕃ⁿ`, and a cube of
the DNF sits inside `Sol(F)`), and `theta_eq` together with `ptE_mem` exhibits an
inhabitant. So no `samp_fin` field is needed. -/

/-- **The lattice points of a cube are finitely many** — from `ptE_onto`, not
assumed.

`Ttc.Set.ncard` of an infinite set is `0`, so without this the non-degeneracy
`0 < ncard` below would be unobtainable and `eq:almostuniform` would degenerate.
The proof needs no geometry: `ptE` enumerates *all* of `Sol(F) ∩ 𝕃ⁿ`
(`ptE_onto`), a cube of the decomposition sits inside `Sol(F)` (`isDNF`), so the
cube's lattice points are a subset of the range of a function out of a `Fin`. -/
theorem lattice_finite_cube {i : Cube A} (hi : i ∈ T.toDNF T.φ) :
    (region T.M i ∩ fineLattice n (latticeScale T.ρ)).Finite := by
  refine Set.Finite.subset (Set.finite_range T.ptE) ?_
  rintro x ⟨hxr, hxl⟩
  obtain ⟨s, hs⟩ := T.ptE_onto x ⟨(T.isDNF (induced T.M x)).1 ⟨i, hi, hxr⟩, hxl⟩
  exact ⟨s, hs⟩

/-- **A cube with a lattice point in it has a positive lattice count.** The
`hN` hypothesis of `Ttc.TtcProb.theta_window_cube`, discharged. -/
theorem lattice_ncard_pos_cube {i : Cube A} (hi : i ∈ T.toDNF T.φ) {x : Space n}
    (hx : x ∈ region T.M i ∩ fineLattice n (latticeScale T.ρ)) :
    0 < (region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard :=
  (Set.ncard_pos (T.lattice_finite_cube hi)).2 ⟨x, hx⟩

/-! ### The enumeration's finiteness and non-degeneracy are **derived, not assumed**

`Ttc.KV97Sampler` used to carry `idx`, `fintypeIdx`, `nonemptyIdx` and `enum` —
an enumeration of the dilated polytope's integer points, together with the
finiteness and non-emptiness that make it one. None of that is independent
information at the `Ttc.TtcProb` level, and the lemmas below prove it: the
inscribed ball (`ball_subset`, `hgammaHat`) makes `Vol(P(cᵢ)) > 0`, `lem:lattice`
(`Ttc.TtcProb.lattice_cube_hi`, itself proved) turns that into a *positive*
lattice count, and `Ttc.ncard_inter_fineLattice` transports the count to the
dilate. A positive `Set.ncard` is by definition both finiteness and
non-emptiness.

**All four fields have accordingly been deleted.** What made that possible is
that `Ttc.KV97Sampler.sampD_eq` now normalises by a `finsum` over
`10^ρ·P(cᵢ) ∩ ℤⁿ` itself, which needs no `Fintype`; the consumer
`Ttc.TtcProb.samp_almostUniform_subtype` installs the `Fintype` from
`Ttc.TtcProb.dilate_intLattice_finite`, the `Nonempty` from
`Ttc.TtcProb.dilate_intLattice_nonempty`, turns the `finsum` back into a
`Finset.sum` with `finsum_eq_sum_of_fintype`, and takes `Equiv.refl` for the
enumeration. So the sampler interface asserts nothing about the count, and
nothing was lost: `Ttc.TtcProb.exists_idx_enum` records that any `Ttc.TtcProb`
could have supplied the old fields anyway. -/

/-- **Each polytope of the decomposition has positive volume** — from the
inscribed ball of radius `γ̂ > 0` (`ball_subset`, `hgammaHat`) and
`volume_ne_top`. -/
theorem volume_region_pos {i : Cube A} (hi : i ∈ T.toDNF T.φ) :
    0 < (volume (region T.M i)).toReal := by
  refine ENNReal.toReal_pos ?_ (T.volume_ne_top ⟨i, hi⟩)
  have hball : 0 < volume (Metric.ball (T.cen ⟨i, hi⟩) T.gammaHat) :=
    Metric.measure_ball_pos _ _ T.hgammaHat
  exact (lt_of_lt_of_le hball (measure_mono (T.ball_subset ⟨i, hi⟩))).ne'

/-- **Every cube of the decomposition contains a lattice point** — no hypothesis
needed. `Ttc.TtcProb.lattice_cube_hi` bounds `Vol(P(cᵢ))` above by a multiple of
the lattice count, and `Ttc.TtcProb.volume_region_pos` says that volume is
positive, so the count cannot be `0`.

This subsumes `Ttc.TtcProb.lattice_ncard_pos_cube`, which needed a point
exhibited; here the geometry supplies one. -/
theorem lattice_ncard_pos_cube' {i : Cube A} (hi : i ∈ T.toDNF T.φ) :
    0 < (region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard := by
  rcases Nat.eq_zero_or_pos (region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard
    with h | h
  · exfalso
    have hhi := T.lattice_cube_hi hi
    rw [h] at hhi
    simp only [Nat.cast_zero, zero_div, mul_zero] at hhi
    exact absurd hhi (not_le.2 (T.volume_region_pos hi))
  · exact h

/-- The same count on the **dilated integer** side, which is the index set of
`Ttc.KV97Sampler.sampD_eq`'s rejection sum. `Ttc.ncard_inter_fineLattice` is the
transport. -/
theorem dilate_intLattice_ncard_pos (i : {c : Cube A // c ∈ T.toDNF T.φ}) :
    0 < ((latticeScale T.ρ • region T.M i.val) ∩ intLattice n).ncard := by
  rw [← ncard_inter_fineLattice (latticeScale_pos T.ρ)]
  exact T.lattice_ncard_pos_cube' i.property

/-- **The former `fintypeIdx`, derived.** A set of positive `Set.ncard` is
finite — an infinite set has `ncard = 0`. -/
theorem dilate_intLattice_finite (i : {c : Cube A // c ∈ T.toDNF T.φ}) :
    ((latticeScale T.ρ • region T.M i.val) ∩ intLattice n).Finite :=
  Set.finite_of_ncard_ne_zero (T.dilate_intLattice_ncard_pos i).ne'

/-- **The former `nonemptyIdx`, derived.** -/
theorem dilate_intLattice_nonempty (i : {c : Cube A // c ∈ T.toDNF T.φ}) :
    ((latticeScale T.ρ • region T.M i.val) ∩ intLattice n).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (T.dilate_intLattice_ncard_pos i).ne'

/-- **`idx`, `fintypeIdx`, `nonemptyIdx` and `enum` were all derivable** — which
is why `Ttc.KV97Sampler` no longer has them.

Every `Ttc.TtcProb` can supply the enumeration the sampler used to carry: take
the subtype itself and the identity equivalence. This lemma is the record of
that, kept because it states the redundancy in one place; the live uses are
`Ttc.TtcProb.dilate_intLattice_finite` and
`Ttc.TtcProb.dilate_intLattice_nonempty` in
`Ttc.TtcProb.samp_almostUniform_subtype`. -/
theorem exists_idx_enum (i : {c : Cube A // c ∈ T.toDNF T.φ}) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι),
      Nonempty (ι ≃ ((latticeScale T.ρ • region T.M i.val) ∩ intLattice n :
        Set (Space n))) :=
  ⟨_, (T.dilate_intLattice_finite i).fintype,
    (T.dilate_intLattice_nonempty i).to_subtype, ⟨Equiv.refl _⟩⟩

/-- **`eq:almostuniform` for the sampler, per cube — the former field, now a
theorem.**

This is where the Kannan–Vempala development becomes load-bearing. Every
hypothesis of `Ttc.almostUniform_of_kv97_density` is supplied by the
`Ttc.KV97Sampler` the problem carries:

* the enumeration and its non-degeneracy — **no longer fields at all**:
  `Ttc.TtcProb.dilate_intLattice_finite` and
  `Ttc.TtcProb.dilate_intLattice_nonempty` supply the `Fintype` and the
  `Nonempty`, and the equivalence is `Equiv.refl` on the set itself;
* `0 < V` — `contVol_pos`, transported to `Vol(P')` by `contVol_eq`;
* `Vol(P') ≠ 0` and `Vol(P') ≠ ∞` — `Ttc.KV97Sampler.volume_inflated_ne_zero` and
  `volume_inflated_ne_top`, both derived from those same two fields;
* `0 < ε'` and `ε' ≤ 1/2` — `Ttc.TtcProb.epsPrime_pos'` and
  `Ttc.TtcProb.epsPrime_le_one_half`, both proved, neither a field;
* the total-variation bound on the *continuous* draw at `ε'/(4·Vol(P'))` —
  `law_tv`;
* the escape mass — **not** a field: `Ttc.escape_of_mem_body`, from `dilate_eq`;
* the normalisation — `sampD_eq`, definitionally the `Dint` below.

The conclusion is `Ttc.AlmostUniform`, whose unfolding is exactly the statement
`Ttc.TtcProb.samp_unif` below. -/
theorem samp_almostUniform_subtype (i : {c : Cube A // c ∈ T.toDNF T.φ}) :
    AlmostUniform (T.sampD i.val)
      (region T.M i.val ∩ fineLattice n (latticeScale T.ρ)) T.P.epsPrime := by
  letI : Fintype ((latticeScale T.ρ • region T.M i.val) ∩ intLattice n : Set (Space n)) :=
    (T.dilate_intLattice_finite i).fintype
  haveI : Nonempty ((latticeScale T.ρ • region T.M i.val) ∩ intLattice n : Set (Space n)) :=
    (T.dilate_intLattice_nonempty i).to_subtype
  haveI : IsProbabilityMeasure (T.sampler.contLaw i) := T.sampler.isProbContLaw i
  have hVpos : 0 < (volume (Arlib.KV97.inflated (T.sampler.Amat i) (T.sampler.bvec i)
      (Arlib.KV97.cOf T.P.epsPrime) T.sampler.facetBound)).toReal := by
    rw [← T.sampler.contVol_eq i]; exact T.sampler.contVol_pos i
  have htv : Arlib.TVLe (T.sampler.contLaw i)
      (Arlib.uniformOn volume (Arlib.KV97.inflated (T.sampler.Amat i) (T.sampler.bvec i)
        (Arlib.KV97.cOf T.P.epsPrime) T.sampler.facetBound))
      (ENNReal.ofReal (T.P.epsPrime / (4 *
        (volume (Arlib.KV97.inflated (T.sampler.Amat i) (T.sampler.bvec i)
          (Arlib.KV97.cOf T.P.epsPrime) T.sampler.facetBound)).toReal))) := by
    have h := T.sampler.law_tv i
    rwa [T.sampler.contVol_eq i] at h
  refine almostUniform_of_kv97_law (latticeScale_pos T.ρ) (Equiv.refl _)
    hVpos T.epsPrime_pos' T.epsPrime_le_one_half
    (T.sampler.volume_inflated_ne_zero i) (T.sampler.volume_inflated_ne_top i) rfl htv
    (fun k => escape_of_mem_body _ _ T.sampler.one_le_facetBound
      T.sampler.card_le_facetBound
      (T.sampler.dilate_subset i k.2.1))
    (Dint := fun z =>
      (∫ p, Arlib.Lattice.Rounding.prodTent z p ∂(T.sampler.contLaw i)) /
      ∑ k : ((latticeScale T.ρ • region T.M i.val) ∩ intLattice n : Set (Space n)),
        ∫ p, Arlib.Lattice.Rounding.prodTent (k : Space n) p ∂(T.sampler.contLaw i))
    (fun _ => rfl) ?_
  intro x hx
  rw [T.sampler.sampD_eq i x hx, finsum_eq_sum_of_fintype]

/-- **`eq:almostuniform` — the former `Ttc.TtcProb` field, recovered verbatim.**

The statement is byte-identical to the field it replaces, so `theta_lo`,
`theta_hi` and every other consumer are untouched. What changed is that it is now
*derived*, from `Ttc.KV97Sampler`'s description of how `GenerateSamples` is
built, via `Arlib.KV97.theorem2` and the `ℤⁿ → 𝕃ⁿ` transport. -/
theorem samp_unif : ∀ i ∈ T.toDNF T.φ,
    ∀ x ∈ region T.M i ∩ fineLattice n (latticeScale T.ρ),
    (1 - T.P.epsPrime) / ((region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard : ℝ)
        ≤ T.sampD i x ∧
      T.sampD i x
        ≤ (1 + T.P.epsPrime) /
            ((region T.M i ∩ fineLattice n (latticeScale T.ρ)).ncard : ℝ) :=
  fun i hi => T.samp_almostUniform_subtype ⟨i, hi⟩

/-- **`Ttc.TtcProb.samp_unif` is `eq:almostuniform`.** It is stated with
`Ttc.AlmostUniform` spelled out, because it is the byte-identical replacement of
a `Model/ProblemSetting` field and that file is upstream of
`Ttc/Sampler/Contract.lean`. This theorem is the identification, and it is
`rfl`. -/
theorem samp_almostUniform {i : Cube A} (hi : i ∈ T.toDNF T.φ) :
    AlmostUniform (T.sampD i) (region T.M i ∩ fineLattice n (latticeScale T.ρ))
      T.P.epsPrime :=
  T.samp_unif i hi

/-- **The paper's Invariant** (`analysis.tex:265`), lower half: each lattice
point's level-`0` rate is at least `(1−ε')²(1−ε/8)/10^(ρ·n)`. The **three** error
sources are `GenerateSamples`' `ε'`, `Vol_ED`'s `ε'` and `lem:lattice`'s
`η = ε/8`.

**This was a `Ttc.TtcProb` field.** It is now a theorem with the same statement,
proved from `theta_eq` (which cube the point came from, and that its rate is the
sampler's mass there times that cube's volume estimate) and `samp_unif`
(`eq:almostuniform` for that cube). The `(1−ε')` the sampler contributes is
genuinely two-sided: a one-sided `D(x) ≤ (1+ε')/|·|` would leave this half
unprovable, and with it the lower half of the headline. -/
theorem theta_lo :
    ∀ s, (1 - T.P.epsPrime) ^ 2 * (1 - T.P.eta) / (latticeScale T.ρ) ^ n ≤ T.θ s := by
  intro s
  obtain ⟨i, hi, hreg, hth⟩ := T.theta_eq s
  have hx : T.ptE s ∈ region T.M i ∩ fineLattice n (latticeScale T.ρ) :=
    ⟨hreg, (T.ptE_mem s).2⟩
  rw [hth]
  exact (T.theta_window_cube (D := T.sampD i) (x := T.ptE s) hi
    (T.lattice_ncard_pos_cube hi hx) (T.samp_almostUniform hi) hx).1

/-- **The paper's Invariant**, upper half. Also a former `Ttc.TtcProb` field. -/
theorem theta_hi :
    ∀ s, T.θ s ≤ (1 + T.P.epsPrime) ^ 2 * (1 + T.P.eta) / (latticeScale T.ρ) ^ n := by
  intro s
  obtain ⟨i, hi, hreg, hth⟩ := T.theta_eq s
  have hx : T.ptE s ∈ region T.M i ∩ fineLattice n (latticeScale T.ρ) :=
    ⟨hreg, (T.ptE_mem s).2⟩
  rw [hth]
  exact (T.theta_window_cube (D := T.sampD i) (x := T.ptE s) hi
    (T.lattice_ncard_pos_cube hi hx) (T.samp_almostUniform hi) hx).2

end TtcProb

/-! ## Axiom profile (`CLAUDE.md` §4) -/

#print axioms card_eq_ncard_of_equiv
#print axioms almostUniform_of_ratio_bounds
#print axioms almostUniform_transport
#print axioms almostUniform_of_kv97
#print axioms almostUniform_of_kv97_density
#print axioms escape_of_mem_body
#print axioms exists_kv97_witness
#print axioms almostUniform_of_kv97_window
#print axioms uniformOn_prodTent_window
#print axioms prodTent_window_of_tvLe
#print axioms almostUniform_of_kv97_law
#print axioms KV97Sampler.volume_inflated_ne_zero
#print axioms KV97Sampler.volume_inflated_ne_top
#print axioms prodTent_le_one
#print axioms TtcProb.volume_region_pos
#print axioms TtcProb.lattice_ncard_pos_cube'
#print axioms TtcProb.exists_idx_enum
#print axioms TtcProb.epsPrime_le_five_eighths
#print axioms TtcProb.epsPrime_le_one_half
#print axioms TtcProb.theta_window_cube_of_kv97
#print axioms TtcProb.theta_window_cube_of_kv97_law
#print axioms TtcProb.lattice_finite_cube
#print axioms TtcProb.samp_almostUniform_subtype
#print axioms TtcProb.samp_unif
#print axioms TtcProb.samp_almostUniform
#print axioms TtcProb.theta_lo
#print axioms TtcProb.theta_hi

end Ttc
