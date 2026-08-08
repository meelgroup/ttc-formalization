/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.EndToEnd

/-!
# `Exec/Budget`: the guarantee at a clean `1 − δ`

`Ttc.ttc_volume_endToEnd` (`Exec/EndToEnd`) and `Ttc.ttc_volume_monteCarlo`
(`Exec/VolDischarge`) conclude

```
1 - δ - δ / 4 ≤ (∫⁻ c, trajLaw … ∂(MonteCarlo.coins n)).toReal
```

The extra `δ/4` is **not** slack in the analysis: it is the constructed Monte-Carlo
volume oracle's own failure share (`Ttc.Params.vol_failure_eq`,
`Ttc.measure_mcGood_ge` in `Exec/VolDischarge`), charged on top of the run's own
`δ` by the union bound of `Ttc.union_bound_two` when `volCoins` was integrated out.
That is weaker than the paper, which promises `1 − δ`; and for `δ > 4/5` the number
`1 − δ − δ/4` is `≤ 0`, so the statement certifies nothing at all there.

## The fix: re-budget, do not re-prove

Nothing about the analysis changes.  What changes is **which failure probability the
algorithm is run at**.  The run is currently given `δ` and the oracle `δ/4`,
totalling `5δ/4`; give the run `4δ/5` and the oracle `(4δ/5)/4 = δ/5` instead, and
the two shares sum to `δ` exactly.  Concretely, run at the internal parameter

```
δ₀ := 4 * δ / 5,      so that      1 - δ₀ - δ₀ / 4 = 1 - 4δ/5 - δ/5 = 1 - δ.
```

`Ttc.ttc_volume_clean` below therefore concludes `1 − δ` in the **user's** `δ`,
with no oracle binders and no new hypothesis.

### Why `4δ/5`, and not the `δ/2 : δ/2` split

The 1 : 4 ratio between the run's share and the oracle's is **not a free knob**.
`Ttc.Params.deltaPrime` is hard-wired to `δ/(4m)` (`alg:ttc` line 18) and
`Ttc.measure_mcGood_ge` bounds the bad-coin mass by `m · δ' = δ/4`; the capstone's
conclusion is consequently a function of the *single* parameter `δ₀`, namely
`1 − δ₀ − δ₀/4`.  So the only rescaling that lands on `1 − δ` is `δ₀ = 4δ/5`.  An
even `δ/2 : δ/2` split would need the oracle share `δ₀/4` to equal `δ/2`, i.e.
`δ₀ = 2δ`, which violates the capstone's own side condition `δ₀ ≤ 1` for every
`δ > 1/2` — exactly the regime this file exists to rescue.  `δ₀ = 4δ/5` instead
satisfies `0 < δ₀` and `δ₀ ≤ 1` on all of `0 < δ ≤ 1` with room to spare, so no
side condition is lost.

### Which `δ` is which, in the statement

| occurrence | which `δ` |
| --- | --- |
| `hδ0 : 0 < δ`, `hδ1 : δ ≤ 1` | the **user's** `δ` |
| `hP : P = ttcParams (toDNF φ) n ε (4 * δ / 5) …` | the **internal** `δ₀ = 4δ/5` |
| every `P.epsPrime`, `P.deltaPrime`, `P.thresh`, `P.precision` in the statement | derived from the **internal** `δ₀`, since they are fields of that `P` |
| the conclusion `1 - δ ≤ …` | the **user's** `δ` |

There is no other occurrence of `δ` in the statement.  `ε` is untouched throughout.

## What it costs — see `Ttc.ttc_volume_clean`'s own docstring

The price is quantified there rather than only here: a `5/4` increase in the
Monte-Carlo sample count and an additive `O(1/ε²)` increase in `Thresh`.

## This theorem is **not** dominated by `Ttc.ttc_volume_final`

`Ttc.ttc_volume_final` (`Exec/Final`) has strictly fewer binders — `Exec/CanonPolytope`
discharges the ten polytope-description binders `Jt`, `[Fintype Jt]`, `Am`, `bv`,
`hdil`, `rfac`, `hr1`, `hcard`, `Dm`, `hDbody` from the canonical system read off
`atoms` — and the same `1 − δ`.  It is tempting to conclude that `ttc_volume_clean`
is redundant.  **It is not**, and the reason is visible in the printed types: the two
conclusions are *different propositions*.  Their running-time conjuncts agree
verbatim, but their accuracy conjuncts integrate different measures, because
`Ttc.rates`' sampler-law argument differs:

| | the `sampD` fed to `Ttc.rates` |
| --- | --- |
| `Ttc.ttc_volume_clean` | `Ttc.e2eSampD M (toDNF φ) … P.epsPrime rfac Am bv cen gammaHat Dm` |
| `Ttc.ttc_volume_final` | `Ttc.e2eSampD M (toDNF φ) … P.epsPrime (canonRfac (toDNF φ)) (canonAm atoms (toDNF φ)) (canonBv atoms (toDNF φ) (latticeScale …)) cen gammaHat (canonDm M (toDNF φ) …)` |

So `ttc_volume_final` is the **instantiation** of `ttc_volume_clean` at the canonical
description, one point of a `∀`.  Instantiating cannot recover the `∀`: from
`ttc_volume_final` one cannot derive `ttc_volume_clean`'s statement for a *user-
supplied* `Am`/`bv`, whose `Ttc.e2eSampD` is a different function and whose
`Ttc.trajLaw` is therefore a different measure.  The implication runs the other way —
`ttc_volume_clean` implies `ttc_volume_final`, which is how `Exec/CanonPolytope` and
`Exec/Final` are in fact built.  `ttc_volume_clean` is the strictly stronger of the
two and needs its **own** witness; it does not inherit `Exec/Final`'s.

## Non-vacuity

`Ttc.Box.ttc_volume_clean_box_at` instantiates the clean statement on the box
`[0,c]ⁿ` at **every** `(ε, δ) ∈ (0,1]²`, with no oracle at all.
`Ttc.Box.clean_box_at_nine_tenths` and `Ttc.Box.clean_box_at_one_quarter` pin it to
two structurally different parameter pairs with the achieved bound written as a
**numeral proved positive**, and the first of them sits at `δ = 9/10 ∈ (4/5, 1)`,
where the old bound `1 − δ − δ/4 = −1/8` was vacuous
(`Ttc.Box.old_budget_vacuous_at_nine_tenths` records that comparison).

Those three, however, are proved by **repricing `Ttc.ttc_volume_endToEnd_box_at`**:
their conclusions have `ttc_volume_clean`'s shape but their proofs run through
`Ttc.ttc_volume_endToEnd`, so they do not by themselves exhibit anything satisfying
`ttc_volume_clean`'s hypothesis list.  The witness that does is
`Ttc.Box.atParamsClean_of`, which **applies `Ttc.ttc_volume_clean`** and therefore
discharges all of its hypotheses — the ten included — on the box; and
`Ttc.Box.exists_two_ttc_volume_clean_instances` packages two of those at
`(ε, δ) = (1/3, 9/10)` and `(1/2, 1/4)`, with each achieved budget a numeral proved
strictly positive in the statement.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Set Pointwise

variable {A : Type*} {n : ℕ}

/-! ## The capstones, at the user's `δ` -/

/-- **`thm:volumettc` with the sampler still a binder, at the guarantee `1 − δ`.**

`Ttc.ttc_volume_endToEnd_ofSampler` run at the internal failure parameter
`δ₀ = 4δ/5`: its budget `1 − δ₀ − δ₀/4` is exactly `1 − δ`, because the volume
oracle's own share `δ₀/4 = δ/5` and the run's share `δ₀ = 4δ/5` sum to `δ`.

The binder list is that of `Ttc.ttc_volume_endToEnd_ofSampler`, unchanged; only
`hP` (the parameter block is computed at `4δ/5`) and the conclusion (`1 - δ`, in the
user's `δ`) differ.  See `Ttc.ttc_volume_clean` for the full accounting of what the
rescaling costs — it applies verbatim here. -/
theorem ttc_volume_clean_ofSampler
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε (4 * δ / 5) hε0 hε1 hn hm hr)
    (hlen : ((toDNF φ).length : ℝ) ≤ P.m)
    (hbdd : Bornology.IsBounded (sol M φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (sampD : Cube A → Space n → ℝ)
    (sampler : KV97Sampler A n M (toDNF φ) (P.precision gammaHat) P.epsPrime sampD)
    (big : ∀ c ∈ mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime,
      (1 - P.epsPrime) * P.thresh / 8
        ≤ ∑ s, rates M φ (toDNF φ) (P.precision gammaHat) sampD
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) s) :
    (1 - δ ≤
      (∫⁻ c, trajLaw (rates M φ (toDNF φ) (P.precision gammaHat) sampD
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
  have hδ0' : 0 < 4 * δ / 5 := by linarith
  have hδ1' : 4 * δ / 5 ≤ 1 := by linarith
  obtain ⟨hacc, hrun⟩ :=
    ttc_volume_endToEnd_ofSampler atoms φ ε (4 * δ / 5) hε0 hε1 hδ0' hδ1' hn M M_eq toDNF
      isDNF isPositive hm hr P hP hlen hbdd hcoeff cen gammaHat hgammaHat ball_subset
      sampD sampler big
  -- `1 - (4δ/5) - (4δ/5)/4 = 1 - 4δ/5 - δ/5 = 1 - δ`
  exact ⟨by linarith [hacc], hrun⟩

/-- **`thm:volumettc`, oracle-free, with the guarantee `1 − δ` the paper states.**

`Ttc.ttc_volume_endToEnd` run at the internal failure parameter `δ₀ = 4δ/5`: its
budget `1 − δ₀ − δ₀/4` is exactly `1 − δ`, because the volume oracle's own share
`δ₀/4 = δ/5` and the run's share `δ₀ = 4δ/5` sum to `δ`.

**The binder list is that of `Ttc.ttc_volume_endToEnd`, unchanged** — same binders,
in the same order, no new hypothesis and no reintroduced oracle.  Only two types
differ:

* `hP` now says `P = ttcParams (toDNF φ) n ε (4 * δ / 5) hε0 hε1 hn hm hr`, i.e. the
  parameter block is computed at `4δ/5`, **not** at `δ`.  The `big` hypothesis and
  the running-time conjunct are stated about *that* block.
* the conclusion is `1 - δ ≤ …` rather than `1 - δ - δ / 4 ≤ …`, in the **user's**
  `δ` (the one constrained by `hδ0`, `hδ1`).

**What this does and does not buy.**  It does not improve the analysis; it reprices
it.  It does remove the regime `δ ∈ (4/5, 1]` in which the old bound was `≤ 0` and
therefore said nothing: at `δ = 9/10` the old budget is `−1/8` and the new one is
`1/10` (`Ttc.Box.old_budget_vacuous_at_nine_tenths`).  At `δ = 1` the new bound is
`0`: true and non-negative, but still uninformative.  The statement is informative
exactly on `δ ∈ (0, 1)`, versus `δ ∈ (0, 4/5)` before.

## The price, quantified

Everything `Ttc.Params` derives from `δ` is now derived from `δ₀ = 4δ/5`, so the run
is executed at a `5/4`-tighter internal confidence.  `ε`, `ε' = ε/12`, `η = ε/8`,
`κ` and `γ` are untouched (none depends on `δ`); the two that move are:

* **`P.deltaPrime`.**  `δ' = δ₀/(4m) = δ/(5m)`, against `δ/(4m)` at the old
  budget — multiplied by `4/5`.  Since `Ttc.MonteCarlo.nSamp K ε' δ'` is
  `⌈(ε'² · δ' · q)⁻¹⌉₊ + 1` (`Volume/MonteCarlo`), the **Monte-Carlo sample count
  per polytope goes from `⌈4m/(δ ε'² q)⌉₊ + 1` to `⌈5m/(δ ε'² q)⌉₊ + 1`: a factor
  `5/4`, i.e. a 25 % increase**, in the number of volume samples drawn, and hence in
  the `cVol` term of the running-time conjunct.

* **`P.thresh`.**  `Thresh = max(24·log(24/δ₀)/((1−ε')ε'²), 15·(log(6/δ₀) + log m))`.
  Since `log(24/δ₀) = log(30/δ) = log(24/δ) + log(5/4)`, the first branch grows by
  the **additive** `24·log(5/4)/((1−ε')ε'²) ≈ 5.36/((1−ε')ε'²)`, which at
  `ε' = ε/12` is `≈ 771/(ε²·(1 − ε/12))`; the second branch grows by the additive
  `15·log(5/4) ≈ 3.35`.  So `Thresh` increases **additively by `O(1/ε²)`**, not
  multiplicatively, and the charged bound `m·(cVol + cSample·Thresh)` of the second
  conjunct goes up by `m·cSample·(Thresh(δ₀) − Thresh(δ))` accordingly.

**Caveat that no re-budgeting touches: this route is exponential in the dimension
`n`.**  The volume oracle is rejection sampling into an enclosing ball, so its
sample count `Ttc.MonteCarlo.nSamp` is `Θ(Rⁿ/(ε'²δ'))` — exponential in `n` — and
the lattice enumeration `Ttc.latticeCount` underlying the transcription is likewise
exponential in `n`.  The `5/4` above is a constant factor on top of an already
exponential construction; this file changes the confidence accounting only, and
claims nothing about polynomiality.

**Not implied by `Ttc.ttc_volume_final`.**  That theorem binds fewer hypotheses but
states a *different* conclusion: its accuracy conjunct integrates the trajectory law
of `Ttc.rates … (Ttc.e2eSampD … (canonRfac …) (canonAm …) (canonBv …) … (canonDm …))`,
i.e. this statement at the one canonical description, whereas the conclusion below is
about the `Ttc.e2eSampD` of the **bound** `rfac`, `Am`, `bv`, `Dm`.  A point of a `∀`
does not give back the `∀`; this theorem implies `Ttc.ttc_volume_final` and not
conversely, so it is the stronger of the two and carries its own witness.  See the
module docstring for the side-by-side.

**Non-vacuity.**  `Ttc.Box.atParamsClean_of` discharges every hypothesis of *this*
theorem — the ten polytope-description binders included — on the box `[0,c]ⁿ` at
every `(ε, δ) ∈ (0,1]²`, by applying it; that lemma's docstring tables which box
lemma discharges which hypothesis.  `Ttc.Box.exists_two_ttc_volume_clean_instances`
exhibits two structurally different such instances, at `(1/3, 9/10)` and `(1/2, 1/4)`,
each with the achieved budget a numeral proved strictly positive in the statement.
`Ttc.Box.ttc_volume_clean_box_at`, `Ttc.Box.clean_box_at_nine_tenths` and
`Ttc.Box.clean_box_at_one_quarter` state the same conclusion on the box but are
proved by repricing `Ttc.ttc_volume_endToEnd_box_at`, so they are corroborating, not
the witness. -/
theorem ttc_volume_clean
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε (4 * δ / 5) hε0 hε1 hn hm hr)
    (hlen : ((toDNF φ).length : ℝ) ≤ P.m)
    (hbdd : Bornology.IsBounded (sol M φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    -- a linear description of the dilated regions, and a diameter bound for it
    (Jt : Type) [Fintype Jt]
    (Am : {c : Cube A // c ∈ toDNF φ} → Jt → Space n)
    (bv : {c : Cube A // c ∈ toDNF φ} → Jt → ℝ)
    (hdil : ∀ i, latticeScale (P.precision gammaHat) • region M i.val
      ⊆ Arlib.Polytope.body (Am i) (bv i))
    (rfac : ℝ) (hr1 : 1 ≤ rfac) (hcard : (Fintype.card Jt : ℝ) ≤ rfac)
    (Dm : {c : Cube A // c ∈ toDNF φ} → ℝ)
    (hDbody : ∀ i, ∀ x ∈ Arlib.Polytope.body (Am i) (bv i),
      ∀ y ∈ Arlib.Polytope.body (Am i) (bv i), dist x y ≤ Dm i)
    (big : ∀ c ∈ mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime,
      (1 - P.epsPrime) * P.thresh / 8
        ≤ ∑ s, rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime rfac Am bv cen gammaHat Dm)
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) s) :
    (1 - δ ≤
      (∫⁻ c, trajLaw (rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime rfac Am bv cen gammaHat Dm)
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
  -- the internal failure parameter, and the two side conditions it needs
  have hδ0' : 0 < 4 * δ / 5 := by linarith
  have hδ1' : 4 * δ / 5 ≤ 1 := by linarith
  obtain ⟨hacc, hrun⟩ :=
    ttc_volume_endToEnd atoms φ ε (4 * δ / 5) hε0 hε1 hδ0' hδ1' hn M M_eq toDNF
      isDNF isPositive hm hr P hP hlen hbdd hcoeff cen gammaHat hgammaHat ball_subset
      Jt Am bv hdil rfac hr1 hcard Dm hDbody big
  -- `1 - (4δ/5) - (4δ/5)/4 = 1 - 4δ/5 - δ/5 = 1 - δ`
  exact ⟨by linarith [hacc], hrun⟩

/-- Legacy name for `Ttc.ttc_volume_clean` (referenced from `README.md` and
`AUDIT.md`). -/
alias ttc_volume_endToEnd_delta := ttc_volume_clean

/-! ## Non-vacuity: the box, and numeral instances at two parameter pairs -/

namespace Box

open MeasureTheory Set

/-- **`Ttc.ttc_volume_clean`'s hypotheses are satisfiable, at every
`(ε, δ) ∈ (0,1]²`.**

`Ttc.Box.ttc_volume_endToEnd_box_at` at the internal failure parameter `4δ/5`.  The
witness is the box `[0,c]ⁿ` carrying **no oracle at all** — Monte-Carlo volume
estimates, `Ttc.rates` on top of them, and the lazy ball walk of
`Ttc.kv97SamplerOfBody` as the sampler.

The `δ` in the conclusion `1 - δ ≤ …` is the **user's** `δ`, the one constrained by
`hδ0`/`hδ1`.  Every other occurrence of `δ` in the statement is `4 * δ / 5`: the
box's side `Ttc.Box.sideS`, its precision `Ttc.Box.rhoS`, its parameter block
`Ttc.Box.parS`, its volume estimates `Ttc.Box.volMC` and its sampler law
`Ttc.Box.bxSampD` are all the ones at the tightened internal confidence, so the run
this witnesses is genuinely a `4δ/5`-run — with the `5/4` sample-count increase
quantified in `Ttc.ttc_volume_clean`'s docstring. -/
theorem ttc_volume_clean_box_at (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ ≤
      (∫⁻ c, trajLaw (rates
            (fun a => (boxAtoms n (sideS n hn ε (4 * δ / 5) hε0 hε1) a).halfspace)
            (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε (4 * δ / 5) hε0 hε1)
            (bxSampD n hn ε (4 * δ / 5) hε0 hε1) (volMC n hn ε (4 * δ / 5) hε0 hε1 c))
          {t : ℕ → Fin (latticeCount
              (fun a => (boxAtoms n (sideS n hn ε (4 * δ / 5) hε0 hε1) a).halfspace)
              (boxForm n hn) (rhoS n hn ε (4 * δ / 5) hε0 hε1)) → ℕ |
            ttcOutput (parS n hn ε (4 * δ / 5) hε0 hε1)
                (coveredOracles
                  (fun a => (boxAtoms n (sideS n hn ε (4 * δ / 5) hε0 hε1) a).halfspace)
                  (boxForm n hn) (rhoS n hn ε (4 * δ / 5) hε0 hε1)
                  (volMC n hn ε (4 * δ / 5) hε0 hε1 c))
                Ttc.toDNF (rhoS n hn ε (4 * δ / 5) hε0 hε1) (boxForm n hn) t
              ∈ relErr ε (volSol
                  (fun a => (boxAtoms n (sideS n hn ε (4 * δ / 5) hε0 hε1) a).halfspace)
                  (boxForm n hn))}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (latticeCount
        (fun a => (boxAtoms n (sideS n hn ε (4 * δ / 5) hε0 hε1) a).halfspace)
        (boxForm n hn) (rhoS n hn ε (4 * δ / 5) hε0 hε1)) → ℕ) (cVol cSample thr : ℕ),
      (thr : ℝ) = (parS n hn ε (4 * δ / 5) hε0 hε1).thresh →
      Terminates (parS n hn ε (4 * δ / 5) hε0 hε1)
          (coveredOracles
            (fun a => (boxAtoms n (sideS n hn ε (4 * δ / 5) hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε (4 * δ / 5) hε0 hε1)
            (volMC n hn ε (4 * δ / 5) hε0 hε1 c) t)
          (Ttc.toDNF (boxForm n hn)) →
      runCost (parS n hn ε (4 * δ / 5) hε0 hε1)
          (coveredOracles
            (fun a => (boxAtoms n (sideS n hn ε (4 * δ / 5) hε0 hε1) a).halfspace)
            (boxForm n hn) (rhoS n hn ε (4 * δ / 5) hε0 hε1)
            (volMC n hn ε (4 * δ / 5) hε0 hε1 c) t)
          cVol cSample (rhoS n hn ε (4 * δ / 5) hε0 hε1) (Ttc.toDNF (boxForm n hn))
        ≤ (Ttc.toDNF (boxForm n hn)).length * (cVol + cSample * thr)) := by
  have hδ0' : 0 < 4 * δ / 5 := by linarith
  have hδ1' : 4 * δ / 5 ≤ 1 := by linarith
  obtain ⟨hacc, hrun⟩ := ttc_volume_endToEnd_box_at n hn ε (4 * δ / 5) hε0 hε1 hδ0' hδ1'
  exact ⟨by linarith [hacc], hrun⟩

/-- Legacy name for `Ttc.Box.ttc_volume_clean_box_at`. -/
alias ttc_volume_endToEnd_delta_box_at := ttc_volume_clean_box_at

/-! ### The achieved probability, named

`Ttc.Box.ttc_volume_clean_box_at`'s accuracy conjunct is a bound on one particular
`∫⁻`.  `Ttc.Box.cleanProb` is a **pure abbreviation** for that `∫⁻` — it is literally
the integral, `Ttc.Box.cleanProb_def` says so by `rfl`, and it asserts nothing
whatever.  Naming it is what lets the numeral instances below state the achieved
bound as a numeral without transcribing the integral again.

Its `δ` argument is the **internal** failure parameter: `cleanProb n hn ε δ₀ …` is
the law of the box run executed at `δ₀`.  The lemmas below always feed it
`δ₀ = 4 * δ / 5`. -/
noncomputable def cleanProb (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ENNReal :=
  ∫⁻ c, trajLaw (rates
        (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
        (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
        (bxSampD n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
      {t : ℕ → Fin (latticeCount
          (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
          (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ |
        ttcOutput (parS n hn ε δ hε0 hε1)
            (coveredOracles
              (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
              (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
            Ttc.toDNF (rhoS n hn ε δ hε0 hε1) (boxForm n hn) t
          ∈ relErr ε (volSol
              (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
              (boxForm n hn))}
    ∂(MonteCarlo.coins n)

/-- `Ttc.Box.cleanProb` is the integral of `Ttc.Box.ttc_volume_clean_box_at`'s
accuracy conjunct, on the nose. -/
theorem cleanProb_def (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    cleanProb n hn ε δ hε0 hε1 =
      ∫⁻ c, trajLaw (rates
            (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
            (boxForm n hn) (Ttc.toDNF (boxForm n hn)) (rhoS n hn ε δ hε0 hε1)
            (bxSampD n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
          {t : ℕ → Fin (latticeCount
              (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
              (boxForm n hn) (rhoS n hn ε δ hε0 hε1)) → ℕ |
            ttcOutput (parS n hn ε δ hε0 hε1)
                (coveredOracles
                  (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn) (rhoS n hn ε δ hε0 hε1) (volMC n hn ε δ hε0 hε1 c))
                Ttc.toDNF (rhoS n hn ε δ hε0 hε1) (boxForm n hn) t
              ∈ relErr ε (volSol
                  (fun a => (boxAtoms n (sideS n hn ε δ hε0 hε1) a).halfspace)
                  (boxForm n hn))}
        ∂(MonteCarlo.coins n) := rfl

/-- The same quantity as a real number — the probability the box run's output lands
in `relErr ε (Vol F)`. -/
noncomputable def cleanAcc (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ℝ :=
  (cleanProb n hn ε δ hε0 hε1).toReal

/-- **`Ttc.Box.ttc_volume_clean_box_at`'s accuracy conjunct, restated on the named
probability.**  `1 − δ` is the **user's** budget; the run is the box run at the
internal `4δ/5`. -/
theorem clean_box_acc_ge (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ cleanAcc n hn ε (4 * δ / 5) hε0 hε1 :=
  (ttc_volume_clean_box_at n hn ε δ hε0 hε1 hδ0 hδ1).1

/-! ### Instance 1: `δ = 9/10`, where the old bound certified nothing -/

/-- **The regime the re-budgeting bought.**  Pure arithmetic, stated so that the
comparison is in the library rather than only in prose: at `δ = 9/10` the old budget
`1 − δ − δ/4` is `−1/8`, which is `≤ 0` and therefore a vacuous lower bound on a
`toReal` (every `toReal` is `≥ 0`), while the new budget `1 − δ` is `1/10 > 0`. -/
theorem old_budget_vacuous_at_nine_tenths :
    (1 - (9/10 : ℝ) - (9/10 : ℝ) / 4 = -(1/8) ∧ 1 - (9/10 : ℝ) - (9/10 : ℝ) / 4 ≤ 0)
      ∧ (1 - (9/10 : ℝ) = 1/10 ∧ (0 : ℝ) < 1/10) := by
  norm_num

/-- **Non-vacuity, in the regime that was previously empty: `(ε, δ) = (1/3, 9/10)`.**

`δ = 9/10 ∈ (4/5, 1)`, so `Ttc.ttc_volume_endToEnd`'s budget `1 − δ − δ/4 = −1/8`
said nothing here (`Ttc.Box.old_budget_vacuous_at_nine_tenths`).  The clean budget is
the numeral `1/10`, and it is proved **strictly positive in the statement**, so this
is a genuine lower bound on the probability that the box run's output lands within
`(1 ± 1/3)·Vol(F)`.

The run witnessed is the box `[0,c]ⁿ` at the internal parameter `4·(9/10)/5 = 18/25`,
with **no oracle at all**: Monte-Carlo volume estimates `Ttc.Box.volMC`, `Ttc.rates`
on top of them, and the lazy ball walk `Ttc.Box.bxSampD` as sampler. -/
theorem clean_box_at_nine_tenths (n : ℕ) (hn : 1 ≤ n)
    (hε0 : (0 : ℝ) < 1/3) (hε1 : (1/3 : ℝ) ≤ 1) :
    (0 : ℝ) < 1/10 ∧ (1/10 : ℝ) ≤ cleanAcc n hn (1/3) (4 * (9/10) / 5) hε0 hε1 := by
  refine ⟨by norm_num, ?_⟩
  have h := clean_box_acc_ge n hn (1/3) (9/10) hε0 hε1 (by norm_num) (by norm_num)
  linarith

/-- **The guarantee at `δ = 9/10` is a genuine number, not `ENNReal.toReal ⊤ = 0`.**

`ENNReal.toReal ⊤ = 0`, so a positive lower bound on the `toReal` forces the integral
itself to be nonzero and finite.  At `δ = 9/10` the old theorem could not conclude
this — its budget there was negative. -/
theorem clean_box_prob_pos_ne_top_at_nine_tenths (n : ℕ) (hn : 1 ≤ n)
    (hε0 : (0 : ℝ) < 1/3) (hε1 : (1/3 : ℝ) ≤ 1) :
    0 < cleanProb n hn (1/3) (4 * (9/10) / 5) hε0 hε1
      ∧ cleanProb n hn (1/3) (4 * (9/10) / 5) hε0 hε1 ≠ ⊤ := by
  have h := (clean_box_at_nine_tenths n hn hε0 hε1).2
  have hpos : 0 < (cleanProb n hn (1/3) (4 * (9/10) / 5) hε0 hε1).toReal := by
    have : (0 : ℝ) < 1/10 := by norm_num
    exact lt_of_lt_of_le this h
  exact ⟨(ENNReal.toReal_pos_iff.1 hpos).1, (ENNReal.toReal_pos_iff.1 hpos).2.ne⟩

/-! ### Instance 2: `δ = 1/4`, a structurally different parameter pair -/

/-- **Non-vacuity at a second, structurally different pair: `(ε, δ) = (1/2, 1/4)`.**

Different accuracy *and* different confidence from
`Ttc.Box.clean_box_at_nine_tenths`, so the parameters are not forced: the internal
run is at `4·(1/4)/5 = 1/5` rather than `18/25`, hence `Ttc.Box.sideS`,
`Ttc.Box.rhoS` and `Ttc.Box.parS` — the box, its precision and its parameter block —
are different objects in the two instances.  The achieved bound is the numeral `3/4`,
proved strictly positive in the statement. -/
theorem clean_box_at_one_quarter (n : ℕ) (hn : 1 ≤ n)
    (hε0 : (0 : ℝ) < 1/2) (hε1 : (1/2 : ℝ) ≤ 1) :
    (0 : ℝ) < 3/4 ∧ (3/4 : ℝ) ≤ cleanAcc n hn (1/2) (4 * (1/4) / 5) hε0 hε1 := by
  refine ⟨by norm_num, ?_⟩
  have h := clean_box_acc_ge n hn (1/2) (1/4) hε0 hε1 (by norm_num) (by norm_num)
  linarith

/-! ### The pair, packaged — as a witness for `Ttc.ttc_volume_clean` itself

`Ttc.Box.AtParamsE2E` (`Exec/EndToEnd`) is **not** a witness for
`Ttc.ttc_volume_clean`.  It binds a bare `sampD` together with a
`Nonempty (Ttc.KV97Sampler …)` — that is the binder shape of
`Ttc.ttc_volume_endToEnd_ofSampler`, one rung *below* `Ttc.ttc_volume_endToEnd` — and
it mentions **none** of the ten polytope-description binders `Jt`, `[Fintype Jt]`,
`Am`, `bv`, `hdil`, `rfac`, `hr1`, `hcard`, `Dm`, `hDbody` that
`Ttc.ttc_volume_clean` actually quantifies over.  Nor does it tie its `sampD` to
`Ttc.e2eSampD` at any description.  So `Ttc.Box.AtParamsE2E` certifies an
intermediate, not this file's theorem.

`Ttc.Box.AtParamsClean` below is the package **for `Ttc.ttc_volume_clean`**: it
carries the ten as fields, ties the sampler law to `Ttc.e2eSampD` at exactly that
description, and carries the clean `1 − δ` accuracy bound together with `alg:ttc`'s
charged cost.  `Ttc.Box.atParamsClean_of` is proved by **applying
`Ttc.ttc_volume_clean`** — every one of its hypotheses, the ten included, is
discharged there on the box `[0,c]ⁿ`.
-/

/-- **`Ttc.ttc_volume_clean`'s hypotheses *and* conclusion, with `(ε, δ)` exposed.**

Everything `Ttc.ttc_volume_clean` quantifies over that is not fixed by the box's own
geometry travels with the package, in particular the **ten polytope-description
binders**:

* `Jt`, `instJt : Fintype Jt`, `Am`, `bv` — the linear system;
* `hdil` — its body contains the *dilated* region of each cube.  Together with
  `hDbody` this rules out the trivial `Am = 0` (whose body is all of `Space n`, of
  infinite diameter) and any body too small to contain the dilated region;
* `rfac`, `1 ≤ rfac`, `(Fintype.card Jt : ℝ) ≤ rfac` — the facet bound;
* `Dm`, `hDbody` — a diameter bound for those bodies.

and the ties that make the statement about the *constructed* sampler rather than an
assumed one: the sampler law is `Ttc.e2eSampD … rfac Am bv cen gammaHat Dm` at
exactly this description, a `Ttc.KV97Sampler` for it **exists**, and the rates built
on it are **strictly positive** at every coin the volume oracle got right — so the
collapsed `θ ≡ 0`, which would satisfy the accuracy conjunct's shape vacuously and
fail `big`, cannot inhabit this.

`P.δ = 4 * δ / 5` is the **internal** failure parameter; the accuracy conjunct is at
the **user's** `1 − δ`.  This asserts nothing on its own: every field is discharged
in `Ttc.Box.atParamsClean_of` by applying `Ttc.ttc_volume_clean` to the box. -/
def AtParamsClean (n : ℕ) (ε δ : ℝ) : Prop :=
  ∃ (atoms : (Fin n ⊕ Fin n) → LinAtom n) (φ : BForm (Fin n ⊕ Fin n)) (P : Params)
      (gammaHat : ℝ)
      (cen : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF φ} → Space n)
      (Jt : Type) (instJt : Fintype Jt)
      (Am : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF φ} → Jt → Space n)
      (bv : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF φ} → Jt → ℝ)
      (rfac : ℝ) (Dm : {cu : Cube (Fin n ⊕ Fin n) // cu ∈ Ttc.toDNF φ} → ℝ),
    0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧ P.ε = ε ∧ P.δ = 4 * δ / 5 ∧ P.n = n ∧ 0 < gammaHat ∧
    Bornology.IsBounded (sol (fun a => (atoms a).halfspace) φ) ∧
    (∀ i, Metric.ball (cen i) gammaHat ⊆ region (fun a => (atoms a).halfspace) i.val) ∧
    -- the ten polytope-description binders of `Ttc.ttc_volume_clean`, discharged
    (∀ i, latticeScale (P.precision gammaHat) •
        region (fun a => (atoms a).halfspace) i.val ⊆ Arlib.Polytope.body (Am i) (bv i)) ∧
    (1 : ℝ) ≤ rfac ∧ ((@Fintype.card Jt instJt : ℕ) : ℝ) ≤ rfac ∧
    (∀ i, ∀ x ∈ Arlib.Polytope.body (Am i) (bv i),
      ∀ y ∈ Arlib.Polytope.body (Am i) (bv i), dist x y ≤ Dm i) ∧
    -- the sampler for *that* description exists, and the rates it induces are positive
    Nonempty (KV97Sampler (Fin n ⊕ Fin n) n (fun a => (atoms a).halfspace) (Ttc.toDNF φ)
      (P.precision gammaHat) P.epsPrime
      (e2eSampD (fun a => (atoms a).halfspace) (Ttc.toDNF φ) (P.precision gammaHat)
        P.epsPrime rfac Am bv cen gammaHat Dm)) ∧
    (∀ c ∈ mcGood (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
        P.epsPrime P.deltaPrime,
      ∀ s, 0 < rates (fun a => (atoms a).halfspace) φ (Ttc.toDNF φ) (P.precision gammaHat)
        (e2eSampD (fun a => (atoms a).halfspace) (Ttc.toDNF φ) (P.precision gammaHat)
          P.epsPrime rfac Am bv cen gammaHat Dm)
        (mcVol (fun a => (atoms a).halfspace) (Ttc.toDNF φ) cen gammaHat
          P.epsPrime P.deltaPrime c) s) ∧
    -- `Ttc.ttc_volume_clean`'s accuracy conjunct, at the user's `1 − δ`
    (1 - δ ≤
      (∫⁻ c, trajLaw (rates (fun a => (atoms a).halfspace) φ (Ttc.toDNF φ)
            (P.precision gammaHat)
            (e2eSampD (fun a => (atoms a).halfspace) (Ttc.toDNF φ) (P.precision gammaHat)
              P.epsPrime rfac Am bv cen gammaHat Dm)
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
    -- and `Ttc.ttc_volume_clean`'s running-time conjunct
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

/-- **`Ttc.ttc_volume_clean` is instantiable at every `(ε, δ) ∈ (0,1]²`, ten binders
included.**

Proved by **applying `Ttc.ttc_volume_clean`** to the box `[0,c]ⁿ` with
`c = max 1 Thresh(ε, 4δ/5)`.  Every hypothesis of that theorem is discharged here,
by name:

| hypothesis | discharged by |
| --- | --- |
| `M_eq`, `hP` | `rfl` |
| `isDNF`, `isPositive` | `Ttc.toDNF_isDNFOf`, `Ttc.toDNF_isPositive` |
| `hm`, `hr` | `Ttc.Box.one_le_card_cubes_box`, `Ttc.Box.one_le_card_facets_box` |
| `hlen` | `Ttc.Box.hlen_box` |
| `hbdd`, `hcoeff` | `Ttc.Box.isBounded_sol_bxOf`, `Ttc.Box.coeff_ne_zero_bxOf` |
| `hgammaHat`, `ball_subset` | `Ttc.Box.gamS_pos`, `Ttc.Box.ball_subset_bxOf` |
| `Jt`, `Am`, `bv` | `Fin n ⊕ Fin n`, `Ttc.Box.bxNormal`, `Ttc.Box.bxOffsetOf` |
| `hdil` | `Ttc.Box.hdil_box` |
| `rfac`, `hr1`, `hcard` | `Ttc.Box.bfac`, `Ttc.Box.one_le_bfac`, `Ttc.Box.card_le_bfac` |
| `Dm`, `hDbody` | `Ttc.Box.bxDm`, `Ttc.Box.hDbody_box` |
| `big` | `Ttc.Box.big_ballWalk_box` |

There is **no oracle**: the volume estimates are the Monte-Carlo oracle's own output
`Ttc.Box.volMC`, the rates are `Ttc.rates` on top of them, and the sampler is the
lazy ball walk `Ttc.Box.bxSampler`, whose one quantitative field is a theorem.

The `δ` in the conclusion is the **user's**; every box object is at the internal
`4δ/5`. -/
theorem atParamsClean_of (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : AtParamsClean n ε δ := by
  have hδ0' : 0 < 4 * δ / 5 := by linarith
  have hδ1' : 4 * δ / 5 ≤ 1 := by linarith
  obtain ⟨hacc, hrun⟩ :=
    ttc_volume_clean (boxAtoms n (sideS n hn ε (4 * δ / 5) hε0 hε1)) (boxForm n hn) ε δ
      hε0 hε1 hδ0 hδ1 hn
      (fun a => (boxAtoms n (sideS n hn ε (4 * δ / 5) hε0 hε1) a).halfspace) rfl Ttc.toDNF
      (toDNF_isDNFOf _) (toDNF_isPositive (boxForm_isPositive hn))
      (one_le_card_cubes_box n hn) (one_le_card_facets_box n hn)
      (parS n hn ε (4 * δ / 5) hε0 hε1) rfl (hlen_box n hn ε (4 * δ / 5) hε0 hε1)
      (isBounded_sol_bxOf n (sideS n hn ε (4 * δ / 5) hε0 hε1) hn)
      (coeff_ne_zero_bxOf n (sideS n hn ε (4 * δ / 5) hε0 hε1) hn)
      (cenMC n hn ε (4 * δ / 5) hε0 hε1) (gamS n hn ε (4 * δ / 5) hε0 hε1)
      (gamS_pos hn hε0 hε1)
      (ball_subset_bxOf n (sideS n hn ε (4 * δ / 5) hε0 hε1) hn)
      (Fin n ⊕ Fin n) (fun _ => bxNormal n)
      (fun _ => bxOffsetOf n (sideS n hn ε (4 * δ / 5) hε0 hε1)
        (rhoS n hn ε (4 * δ / 5) hε0 hε1))
      (hdil_box n hn ε (4 * δ / 5) hε0 hε1) (bfac n) one_le_bfac card_le_bfac
      (bxDm n hn ε (4 * δ / 5) hε0 hε1) (hDbody_box n hn ε (4 * δ / 5) hε0 hε1)
      (big_ballWalk_box n hn ε (4 * δ / 5) hε0 hε1 hδ0' hδ1')
  exact ⟨boxAtoms n (sideS n hn ε (4 * δ / 5) hε0 hε1), boxForm n hn,
    parS n hn ε (4 * δ / 5) hε0 hε1, gamS n hn ε (4 * δ / 5) hε0 hε1,
    cenMC n hn ε (4 * δ / 5) hε0 hε1, Fin n ⊕ Fin n, inferInstance,
    (fun _ => bxNormal n),
    (fun _ => bxOffsetOf n (sideS n hn ε (4 * δ / 5) hε0 hε1)
      (rhoS n hn ε (4 * δ / 5) hε0 hε1)),
    bfac n, bxDm n hn ε (4 * δ / 5) hε0 hε1,
    hε0, hε1, hδ0, hδ1, rfl, rfl, rfl, gamS_pos hn hε0 hε1,
    isBounded_sol_bxOf n (sideS n hn ε (4 * δ / 5) hε0 hε1) hn,
    ball_subset_bxOf n (sideS n hn ε (4 * δ / 5) hε0 hε1) hn,
    hdil_box n hn ε (4 * δ / 5) hε0 hε1, one_le_bfac, card_le_bfac,
    hDbody_box n hn ε (4 * δ / 5) hε0 hε1,
    ⟨bxSampler n hn ε (4 * δ / 5) hε0 hε1⟩,
    fun c hc s => bxRates_pos n hn ε (4 * δ / 5) hε0 hε1 c hc s, hacc, hrun⟩

/-- **`ε` and `δ` are not forced, and both instances are informative at the
user-facing budget `1 − δ`.**

Two instances of **`Ttc.ttc_volume_clean` itself** — `Ttc.Box.AtParamsClean` carries
its ten polytope-description binders as discharged fields, its `Ttc.e2eSampD`-tied
sampler law, the `Nonempty` ball walk, strict positivity of the constructed rates,
and its `1 − δ` conclusion (see `Ttc.Box.atParamsClean_of` for the hypothesis-by-name
table).  `Ttc.Box.AtParamsE2E` is carried alongside for continuity, but it is the
*weaker* package: it is `Ttc.ttc_volume_endToEnd_ofSampler`-shaped and knows nothing
of the ten.

The point of the first pair is that `δ₁ = 9/10` lies in `(4/5, 1)`: there the old
budget `1 − δ₁ − δ₁/4 = −1/8` is not positive and certifies nothing, while the clean
budget is `1/10`.  The second pair `(1/4, 1/4)` is informative under both.

The two runs are structurally different, not two names for one instance: `ε₁ ≠ ε₂`,
`δ₁ ≠ δ₂`, and the internal parameters differ too (`18/25 ≠ 1/5`), so
`Ttc.Box.sideS`, `Ttc.Box.rhoS` and `Ttc.Box.parS` — the box, its precision and its
parameter block, hence also `Am`, `bv` and `Dm` — are different objects in the two.
Each achieved budget is pinned to a **numeral proved strictly positive here in the
statement**, so neither is the vacuous `0 ≤ toReal`. -/
theorem exists_two_ttc_volume_clean_instances (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε₁ δ₁ ε₂ δ₂ : ℝ,
      AtParamsClean n ε₁ δ₁ ∧ AtParamsClean n ε₂ δ₂ ∧
      AtParamsE2E n ε₁ (4 * δ₁ / 5) ∧ AtParamsE2E n ε₂ (4 * δ₂ / 5) ∧
      ε₁ ≠ ε₂ ∧ δ₁ ≠ δ₂ ∧ 4 * δ₁ / 5 ≠ 4 * δ₂ / 5 ∧
      (0 < ε₁ ∧ ε₁ < 1) ∧ (0 < δ₁ ∧ δ₁ < 1) ∧
      (0 < ε₂ ∧ ε₂ < 1) ∧ (0 < δ₂ ∧ δ₂ < 1) ∧
      -- the packaged budget at the internal parameter *is* `1 − δᵢ` in the user's `δᵢ`
      1 - (4 * δ₁ / 5) - (4 * δ₁ / 5) / 4 = 1 - δ₁ ∧
      1 - (4 * δ₂ / 5) - (4 * δ₂ / 5) / 4 = 1 - δ₂ ∧
      -- each user-facing budget, as a numeral, proved positive
      1 - δ₁ = 1 / 10 ∧ 1 - δ₂ = 3 / 4 ∧ 0 < 1 - δ₁ ∧ 0 < 1 - δ₂ ∧
      -- and the first sits where the *old* budget was vacuous
      4 / 5 < δ₁ ∧ 1 - δ₁ - δ₁ / 4 = -(1/8) ∧ 1 - δ₁ - δ₁ / 4 ≤ 0 :=
  ⟨1/3, 9/10, 1/2, 1/4,
    atParamsClean_of n hn (1/3) (9/10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    atParamsClean_of n hn (1/2) (1/4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    atParamsE2E_of n hn (1/3) (4 * (9/10) / 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    atParamsE2E_of n hn (1/2) (4 * (1/4) / 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    by norm_num, by norm_num, by norm_num,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

end Box

/-! ## Axiom profile

`CLAUDE.md` §4.  Expect `[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms ttc_volume_clean_ofSampler
#print axioms ttc_volume_clean
#print axioms ttc_volume_endToEnd_delta
#print axioms Box.ttc_volume_clean_box_at
#print axioms Box.ttc_volume_endToEnd_delta_box_at
#print axioms Box.cleanProb
#print axioms Box.cleanProb_def
#print axioms Box.cleanAcc
#print axioms Box.clean_box_acc_ge
#print axioms Box.old_budget_vacuous_at_nine_tenths
#print axioms Box.clean_box_at_nine_tenths
#print axioms Box.clean_box_prob_pos_ne_top_at_nine_tenths
#print axioms Box.clean_box_at_one_quarter
#print axioms Box.AtParamsClean
#print axioms Box.atParamsClean_of
#print axioms Box.exists_two_ttc_volume_clean_instances

end Ttc
