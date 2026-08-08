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

## Non-vacuity

`Ttc.Box.ttc_volume_clean_box_at` instantiates the clean statement on the box
`[0,c]ⁿ` at **every** `(ε, δ) ∈ (0,1]²`, with no oracle at all.
`Ttc.Box.clean_box_at_nine_tenths` and `Ttc.Box.clean_box_at_one_quarter` pin it to
two structurally different parameter pairs with the achieved bound written as a
**numeral proved positive**, and the first of them sits at `δ = 9/10 ∈ (4/5, 1)`,
where the old bound `1 − δ − δ/4 = −1/8` was vacuous
(`Ttc.Box.old_budget_vacuous_at_nine_tenths` records that comparison).
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

**Non-vacuity.**  `Ttc.Box.ttc_volume_clean_box_at` discharges every hypothesis on
the box at every `(ε, δ) ∈ (0,1]²`, and `Ttc.Box.clean_box_at_nine_tenths` /
`Ttc.Box.clean_box_at_one_quarter` do so at two numeral parameter pairs with the
achieved bound proved positive. -/
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

/-! ### The pair, packaged -/

/-- **`ε` and `δ` are not forced, and both instances are informative at the
user-facing budget `1 − δ`.**

Two end-to-end instances at *different* accuracy pairs.  `Ttc.Box.AtParamsE2E n ε δ₀`
is the package of `Ttc/Exec/EndToEnd.lean` — it carries the parameter block, the
boundedness of the solution set, `γ̂ > 0`, a **`Nonempty` ball-walk sampler**, strict
positivity of the constructed rates, and the accuracy bound `1 − δ₀ − δ₀/4`.  Here it
is instantiated at the *internal* parameter `δ₀ = 4δᵢ/5`, so the bound it carries is
exactly `1 − δᵢ` in the user's `δᵢ` — recorded by the `budget` equations below, which
pin each to a **numeral proved positive**.

The point of the first pair is that `δ₁ = 9/10` lies in `(4/5, 1)`: there the old
budget `1 − δ₁ − δ₁/4 = −1/8` is not positive and certifies nothing, while the clean
budget is `1/10`.  The second pair `(1/4, 1/4)` is informative under both.

The two runs are structurally different, not two names for one instance: `ε₁ ≠ ε₂`,
`δ₁ ≠ δ₂`, and the internal parameters differ too (`18/25 ≠ 1/5`). -/
theorem exists_two_ttc_volume_clean_instances (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε₁ δ₁ ε₂ δ₂ : ℝ,
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
#print axioms Box.exists_two_ttc_volume_clean_instances

end Ttc
