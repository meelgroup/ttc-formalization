/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.PolyAccuracy
import Ttc.Exec.PricedHeadline

/-!
# `Exec/RuntimeMN4`: the **goal-state capstone**, and the ledger of what it still assumes

One theorem — `Ttc.ttc_runtime_mn4` — about **one run** of `Ttc.ttcPoly` (the
oracle-swapped bundle: Cousins–Vempala volume, hit-and-run sampling), with two conjuncts:

* **accuracy** `1 − δ ≤ Pr[ output ∈ (1 ± ε)·Vol(F) ]`, and
* **runtime** `All[ charged cost ≤ m · n⁴ · (explicit factors) ]`,

and **every** residual mathematical input as an explicit, named, visible binder.  This is
`CLAUDE.md` §1's "interface → instance → capstone" run to its end state: the capstone
exists *now*, carrying its debts in its own type, and each later discharge deletes one
binder.  §"The ledger" below is therefore the project's progress metric — the number to
watch is the **38 residual hypotheses**, and a change to this file that does not move that
number is not progress.

> ## ⚠ THIS THEOREM DOES **NOT** PROVE THAT `TTC` RUNS IN `O(m·n⁴)` ⚠
>
> Read this before quoting any number below.  Five independent reasons, each of which
> alone is fatal to the unconditional reading:
>
> 1. **The charged cost is an undercount.**  `Ttc.ttcPolyCost` charges **one unit per
>    oracle call** and nothing else.  It prices at **zero** the arithmetic performed
>    *inside* a call, the rejection rounds of the sampler, and `alg:ttc`'s lines 32–42
>    `while` loops.  `r.2` is a call count with unit prices attached, not a running time.
> 2. **This is `Ttc.ttcPoly`, not `Ttc.ttc`.**  `Ttc/Model/Theorem.lean`'s headline runs
>    `Ttc.algOracles` — hit-and-miss Monte Carlo over the lazy ball walk — and the prices
>    that run *can* be shown to pay (`Ttc.ttcVolPrice`, `Ttc.ttcSampPrice`) are
>    **exponential in `n`**.  `Ttc.ttcPoly` is a **different program**: the volume coins
>    come from `V.μ` and the rates carry the hit-and-run law.  Swapping the oracles is a
>    modelling choice; see `Ttc/Exec/PricedHeadline.lean:18-50`.
> 3. **The accuracy conjunct is conditional**, on all 38 hypotheses of the ledger — most
>    sharply on `H : Ttc.HitAndRunTheorem11Input`, which is **inhabited nowhere** in this
>    development, and on `hphase_mean`/`hphase_var`, Cousins–Vempala's residual *sampler*
>    hypotheses.  `hphase_mean` is now the interval a total-variation bound can actually
>    deliver rather than an equation, so it has a route (§C, row 12); nothing in this
>    repository walks that route, because the route needs a sampler with a proved TV bound.
> 4. **The warm start is assumed.**  `hMw1`/`hMwB` (`1 ≤ M ≤ (2R)ⁿ`) is a genuine open
>    hypothesis — `Ttc/Exec/SampPriceHR.lean:316` records that nothing in this repository
>    constructs a warm start at any `M`.
> 5. **The regime caveat: `n⁴` needs a temperature-scale body (`R = O(σ)`).**  In the
>    Cousins–Vempala regime `R ≍ σ√n` the conductance floor forces a smaller step, the
>    per-draw cost becomes `n⁴` and the total `n⁵`; and
>    `Arlib.MarkovChains.exists_halfspace_max_lt` proves that the obvious route to
>    recovering the missing `√n` is **false**, not merely open.
>
> What *is* established: **at the two fixed per-call prices, under the 38 listed
> hypotheses, the swapped run's call-count cost is at most `m·n⁴·(…)` almost surely, and
> its output is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`.**  Nothing more.

## What this file adds over `Ttc.ttcPoly_volume_estimate_cv`

`Ttc.ttcPoly_volume_estimate_cv` (`Exec/PolyAccuracy.lean:751`) already states these two
conjuncts about this run.  `Ttc.ttc_runtime_mn4` is that statement

* with the volume oracle **rebuilt on the weaker phase-mean hypothesis**.
  `Ttc.ttcPoly_volume_estimate_cv` runs on `Ttc.cvVolAlg`, i.e.
  `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns`, whose `hphase_mean` is an **equation**
  `∫ g dν = chain(i+1)/chain(i)`; no mixing bound can ever discharge an equation
  (`Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne` is the
  machine-checked negative).  This theorem runs on
  `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`
  (`Volume/CVInstantiate.lean`), whose `hphase_mean` is the **interval**
  `∫ g dν ∈ (1 ± ε/(2(2+ε)m))·(chain(i+1)/chain(i))` — the shape a total-variation bound
  on a sampler delivers, and the shape `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler`
  *derives* from `hTV`.  The two constructors produce the **same** `Ω`, `μ` and `est`, and
  the `VolumeAlgorithm` guarantee they establish is character-for-character the same, so
  the run and both conjuncts below are unchanged; only the hypothesis is weaker.  The one
  binder that had to move with it is `hphase_var`, now stated at
  `Arlib.GaussianCooling.varBudget (ε/2)` — see ledger row 13;
* **renamed** to the goal-state name, so the ledger has a stable referent;
* with **four binders discharged** (68 explicit → 64): `hrfac`, `hep0`, `hep1`, `heps1`.
  All four are theorems of this repository at hypotheses the capstone already carries —
  `Ttc.one_le_canonRfac_preprocess` (`Exec/PolyAccuracy.lean:240`),
  `Ttc.algBlock_epsPrime_pos` (`Exec/PriceList.lean:226`, unconditional),
  `Ttc.algBlock_epsPrime_le_one` (`Exec/SampPriceHR.lean:182`, unconditional) and
  `Ttc.ttcSampTol_le_one` (`Exec/SampleDischarge.lean:510`, which applies to the
  hit-and-run start data with **no bridging** — see `Ttc.ttc_runtime_mn4_tol_le_one`).
  Carrying them was an accounting error, not an assumption;
* with `Ttc.PolyComplexity.threshFactor` **expanded to closed arithmetic** in the bound,
  so that no project `def` stands between the reader and the number, exactly as
  `Ttc/Model/Theorem.lean:107-128` does.  `Ttc.ttc_runtime_mn4_threshFactor` below proves
  the expansion is the definition (by `rfl`), so nothing is asserted by naming.

## The ledger

> **Counting convention** (the one used at `Ttc/Exec/Endgoal.lean:64-70` — read it before
> "correcting" these numbers).  Every count below is of **explicit** binders.  A probe
> that walks the raw `ConstantInfo.type` counting `Expr.forallE` reports a larger number,
> because the ambient implicits and the instance arguments are binders in the type but are
> not obligations anyone has to discharge.  `#binderProfile` at the foot of this file
> prints all three numbers; quote what it prints, not this sentence.
>
> **68 raw = 64 explicit + 2 implicit (`{A}`, `{n}`) + 2 instance.**
>
> Of the 64 explicit, **26 are data** — things a caller *supplies*, not obligations —
> and **38 are residual hypotheses**.  Of the 2 instance binders, `[MeasurableSpace E]`
> is data and `[∀ j i, IsProbabilityMeasure (ν j i)]` is a (trivial) hypothesis; they are
> counted separately below and are not in the 38.

### The 26 data binders (supplied, not proved)

`atoms φ ε δ` (the algorithm's four inputs); `E ν phases σsq g B` (the Cousins–Vempala
coin space, coordinate laws, schedule and score family); `rin Rout Mw sigma` (the
per-cube hit-and-run start data the run itself takes); `gam R Mwarm Lc kap cc pf Mcool
epsDraw` (the nine complexity parameters); `zin zout Sx` (witnesses inside the
Lovász–Vempala start hypotheses).

### THE 38 RESIDUAL HYPOTHESES

**A. FPRAS parameter range and input conditions — 7.**  These are the hypotheses
`Ttc.ttc_volume_estimate` (`Model/Theorem.lean:95`) also carries; they are conditions on
the *user's* input, not debts of the development, and will never go away.

| # | binder | statement | discharged by |
| --- | --- | --- | --- |
| 1 | `hε0` | `0 < ε` | — (input condition) |
| 2 | `hε1` | `ε ≤ 1` | — (input condition) |
| 3 | `hδ0` | `0 < δ` | — (input condition) |
| 4 | `hδ1` | `δ ≤ 1` | — (input condition) |
| 5 | `hn` | `1 ≤ n` | — (input condition) |
| 6 | `hφ` | `φ.IsPositive` — `F` is a positive Boolean formula | — (`prob:volume`'s standing assumption) |
| 7 | `hpos` | `0 < Vol(Sol(F))` | — (input condition; `Ttc.hint_not_derivable` shows it is not derivable) |

**B. Lovász–Vempala Theorem 1.1 — 1.  OWNER-AUTHORISED TO REMAIN.**

| # | binder | statement | discharged by |
| --- | --- | --- | --- |
| 8 | `H : Ttc.HitAndRunTheorem11Input` | *Hit-and-Run from a Corner* (2005) Thm 1.1: from a warm start, `> 2⁵⁶n²(R²/r²)log(8M/ε²)` hit-and-run transitions land within TV distance `ε` of uniform | **nothing.**  `Ttc/Sampler/HitAndRunTheorem11.lean:94`, structure with one field `mixing` (line 95), **inhabited nowhere**.  Its own proof would rest on Lovász–Simonovits 1993 Cor. 1.5 (`hLS`, also unproved).  Note the repository's constant is `2⁵⁶`, **not** the paper's printed `10¹⁰`, which `Ttc.hitAndRunTheorem11Threshold`'s docstring shows is short by `≈ 2×10⁵` |

**C. Cousins–Vempala's residual sampler hypotheses — 2 (+ 3 side conditions on caller
data).  OWNER-AUTHORISED TO REMAIN.**  The volume oracle here is
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`
(`Ttc/Volume/CVInstantiate.lean:458`), which has already discharged **twelve of
`Ttc.VolumeAlgorithm.cousinsVempala`'s fourteen** hypotheses from `Arlib`
(`Ttc/Volume/CVInstantiate.lean:60-75, 256-263`).  These are the two that remain, plus
the three conditions on the schedule/score data the caller picks anyway.

Note this is **not** `Ttc.cvVolAlg`.  `Ttc.cvVolAlg` is
`Ttc.VolumeAlgorithm.cousinsVempalaOfRuns`, whose `hphase_mean` is an *equation*; the
constructor used here differs from it in exactly that hypothesis (and in the variance
budget the accuracy split forces).  Same coin space, same score, same median selector,
same `est`, same guarantee.

| # | binder | statement | discharged by |
| --- | --- | --- | --- |
| 9 | `hσ` | `0 < σsq K ε p j` — the variance schedule is positive | — (condition on caller-chosen data, e.g. `Arlib.GaussianCooling.geomSchedule`) |
| 10 | `hg` | each score `g K ε p j i` is measurable | — (condition on caller-chosen data) |
| 11 | `hgb` | `|g K ε p j i x| ≤ B` uniformly | — (condition on caller-chosen data; consumed by `Arlib.Probability.memLp_two_natRunProd`) |
| 12 | `hphase_mean` | `∫ g K ε p j i dν ∈ (1 ± ε/(2(2+ε)m))·(chain(i+1)/chain(i))` — the phase-`i` score is unbiased for the phase ratio **up to a relative `Θ(ε/m)`** | **a route, walked by nothing here.**  `Ttc/Volume/CVInstantiate.lean:470`.  `Ttc.CV.sampledPhase_mean_mem_relErr` *derives* exactly this interval from a total-variation guarantee `hTV` on a sampler for `Arlib.GaussianCooling.coolLaw` (see `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler`), so it is no longer a hypothesis nothing could ever discharge — but no sampler in this repository comes with a proved `hTV` at the accuracy the slack conditions need, so nothing walks the route.  The route does **not** exist for the equation this binder used to be: `Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne` proves the relative error is exactly the TV error, so no mixing bound whatsoever delivers an equality |
| 13 | `hphase_var` | `∫ g² dν ≤ (1 + varBudget (ε/2) / phases)·(∫ g dν)²` | **nothing.**  `Ttc/Volume/CVInstantiate.lean:476`.  A *transport* problem: §5.1 proves the corresponding bound for the **ideal** estimator unconditionally (`Arlib.GaussianCooling.fixed_var_bound_ratio_indicator`).  The budget is `varBudget (ε/2)`, not `varBudget ε`, and that is **forced**: `cousinsVempalaOfApproxMean` splits the requested `ε` into an inner (Chebyshev) accuracy `ε/2` and a mean bias `ε/(2+ε)`, and `Real.exp (varBudget κ) - 1 = κ²/5` must sit under the *inner* accuracy.  Any split with a strictly positive bias tolerance shrinks the variance budget; only the (undischargeable) exact-equation hypothesis keeps the full `varBudget ε` |

**D. The hit-and-run warm start — 9.  OWNER-AUTHORISED TO REMAIN.**  Exactly the
hypotheses `Ttc.kv97SamplerOfHitAndRun` needs to turn `H` into a `Ttc.KV97Sampler`
certificate for `Ttc.polySampD`: an inscribed ball, a circumscribed ball, and the paper's
exceptional-set form of warmness.  (The tenth, the tolerance guard
`heps1 : ε'/(4·Vol(inflated …)) ≤ 1`, is **discharged** here — see
`Ttc.ttc_runtime_mn4_tol_le_one` and `Ttc.ttcSampTol_le_one`,
`Exec/SampleDischarge.lean:510` — and is therefore not in this table.)

| # | binder | statement | discharged by |
| --- | --- | --- | --- |
| 14 | `hrin` | `0 < rin i` — the inscribed radius is positive | — (caller-supplied start data) |
| 15 | `hin` | `closedBall (zin i) (rin i) ⊆ inflated …` — inscribed ball | — (caller-supplied) |
| 16 | `hRout` | `0 ≤ Rout i` | — (caller-supplied) |
| 17 | `hout` | `inflated … ⊆ closedBall (zout i) (Rout i)` — circumscribed ball | — (caller-supplied) |
| 18 | `hsigma` | each start law `sigma i` is a probability measure | — (caller-supplied) |
| 19 | `hM` | `1 ≤ Mw i` — the warmness parameter is `≥ 1` | — (caller-supplied) |
| 20 | `hSm` | the exceptional set `Sx i` is measurable | — (caller-supplied) |
| 21 | `hS` | `sigma i (Sx i) ≤ (ε'/(4·Vol))/2` — the start gives the exceptional set little mass | **nothing.**  This is Thm 1.1's exceptional-start hypothesis in the measure form (`Ttc/Sampler/HitAndRunTheorem11.lean:23-27`) |
| 22 | `hdom` | `sigma i (T \ Sx i) ≤ Mw i · uniform (T \ Sx i)` — off the exceptional set the start is `M`-warm | **nothing.**  Same source |

**E. The sampler-side cost regime — 6.**

| # | binder | statement | discharged by |
| --- | --- | --- | --- |
| 23 | `hR1` | `1 ≤ R` | — (regime condition on the circumradius; `R` is a free binder, so this is a *statement shape*, not a debt) |
| 24 | `hgam0` | `0 < gam` | — (ditto, inradius) |
| 25 | `hgamR` | `gam ≤ R` | — (ditto) |
| 26 | `hMw1` | `1 ≤ Mwarm` | — (ditto, warmness) |
| 27 | `hMwB` | `Mwarm ≤ (2R)ⁿ` — **the warm-start bound** | **nothing, at any `M`.**  `Ttc/Exec/SampPriceHR.lean:316` and `Exec/SamplerCost`'s docstring: "a genuine open hypothesis".  OWNER-AUTHORISED TO REMAIN |
| 28 | `hepn` | `1/2ⁿ ≤ ε'` — the accuracy is not exponentially small | **`Ttc.samplePrice_le_quartic_eps` (`Ttc/Exec/SampPriceEps.lean:183`).**  See "The `hepn` swap" below — this is the binder expected to disappear next, and the only one with a named landing lemma |

**F. The volume-side (Gaussian cooling) cost regime — 10.**  All ten are conditions on
free binders of the *statement* (`Lc kap cc pf Mcool epsDraw`), consumed by
`Ttc.CoolCost.cvVolumeOpsPrice_le_cool`.  None is a debt of the development: they say
which regime the quoted `n⁴` is the cost in.

| # | binder | statement |
| --- | --- | --- |
| 29 | `hL` | `1 ≤ Lc` (the cooling Lipschitz/length constant) |
| 30 | `hkap0` | `0 < kap` |
| 31 | `hkap1` | `kap ≤ 1` (the conductance floor) |
| 32 | `hcc1` | `1 ≤ cc` |
| 33 | `hcc` | `cc ≤ 1 + 2/n` (the cooling ratio is `1 + O(1/n)` — this is *the* Gaussian-cooling schedule condition) |
| 34 | `hp0` | `0 < pf` |
| 35 | `hp1` | `pf ≤ 1/2` (the per-phase failure probability) |
| 36 | `hMc` | `1 ≤ Mcool` (the cooling warm start) |
| 37 | `hed0` | `0 < epsDraw` |
| 38 | `hed1` | `epsDraw ≤ 1` (the per-draw TV tolerance) |

**Instance binders — 2, counted apart.**  `[MeasurableSpace E]` is data;
`[∀ j i, IsProbabilityMeasure (ν j i)]` says each coordinate law is a probability measure
(caller-supplied, trivial).

### Summary count

```
raw ∀-binders                     68
  = explicit                      64
      of which data               26
      of which HYPOTHESES         38   ← the number to watch
  + implicit ({A}, {n})            2
  + instance                       2   (1 data, 1 trivial hypothesis)
```

Of the 38: **7** are the FPRAS input range (A); **15** are the owner-authorised
sampler/volume-oracle block (B + C + D = 1 + 5 + 9); **6** are the sampler-side cost
regime (E), one of which — `hepn`, #28 — has a named landing lemma; **10** are the
volume-side cost regime (F).  `7 + 15 + 6 + 10 = 38`.

Assumptions with **no route to a proof anywhere in this repository** — the honest core of
the debt: #8 (`H`, Lovász–Vempala Thm 1.1), #13 (`hphase_var`, Cousins–Vempala's residual
variance-transport hypothesis), #21 and #22 (`hS`, `hdom`, the warm start's
exceptional-set form), #27 (`hMwB`, the warm-start bound).  **Five.**  Everything else is
an input condition, a condition on caller-chosen schedule/start data, a regime condition
on a free binder of the statement, or scheduled.

#12, `hphase_mean`, has **left that list** and is the one change this file records.  In
its old, equation-carrying form (`∫ g dν = chain(i+1)/chain(i)`, the form
`Ttc.cvVolAlg` still has) it was routeless *in principle*:
`Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne` shows the relative
error of a sampled phase mean is exactly the sampler's TV error, so no mixing theorem —
however strong, short of exact sampling — can ever deliver the equality.  In the interval
form carried here it is routeless only *in practice*:
`Ttc.CV.sampledPhase_mean_mem_relErr` derives it from a TV bound, and
`Ttc.VolumeAlgorithm.cousinsVempalaOfSampler` is the constructor that does so.  What is
missing is the sampler, i.e. a proved `hTV` — the same open problem as #8, not a
separate impossibility.  The residual-hypothesis **count is unchanged at 38**; what
changed is that one of them is now a statement something could prove.

## The `hepn` swap — the one-line change this file is written to accept

Binder #28, `hepn : 1/2ⁿ ≤ ε'`, is carried only because the cost half routes through
`Ttc.all_ttcPoly_cost_le_quartic` (`Exec/PolyRun.lean:535`), which consumes
`Ttc.SamplerCost.samplePrice_le_quartic` (`Exec/SamplerCost.lean:765`) — and *that* lemma
needs `hepn` to fold `log(1/ε')` into `n·log(2R)`.

The owner has ruled that **`ε` may appear in the complexity**, so `hepn` should not be
carried.  `Ttc.samplePrice_le_quartic_eps` (`Ttc/Exec/SampPriceEps.lean:183`, another
agent's file, **not depended on here**) drops it at the cost of an explicit `log(1/ε')`:

```
samplePrice n γ R M ε' rfac ≤ 2⁶² · n³ · rfac · (R²/γ²) · (n·log(2R) + log(1/ε'))
```

The swap, precisely:

1. delete binder `hepn` from `Ttc.ttc_runtime_mn4`;
2. in the runtime conjunct, replace the sampler summand
   `2⁶² · rfac · (R²/γ²) · log(2R) · Thr` by
   `2⁶² · rfac · (R²/γ²) · (n·log(2R) + log(1/ε')) · Thr` and drop one power of `n` from
   the leading `n⁴` (the bound becomes `m · n³ · (…)`, or keep `n⁴` and absorb);
3. re-derive the cost half **inlining what `Ttc.all_ttcPoly_cost_le_quartic` composes** —
   `Ttc.all_ttcPoly_cost_le_ttcComplexity` (`Exec/PolyRun.lean:479`, which carries **no**
   regime binder at all), then `Ttc.CoolCost.cvVolumeOpsPrice_le_cool` for the volume
   price and `Ttc.samplePrice_le_quartic_eps` for the sampler price, combined by
   `Ttc.PolyComplexity.ttcComplexity_le_quartic`.

Nothing else in this file moves: the accuracy conjunct, the data binders and groups
A–D are untouched.  Expected ledger after the swap: **37 residual hypotheses**.

## Non-vacuity (`CLAUDE.md` §11) — reported, not papered over

* `Ttc.isProbabilityMeasure_ttcPoly` (`Exec/PolyRun.lean:448`) — the **measure-level**
  check.  A `MeasureTheory.Measure.bind` of a non-measurable family is the zero measure,
  at which every `All[…]` holds vacuously and every `Pr[…]` is `0`.  That instance rules
  it out, at *every* `V`, hence at the volume oracle used here.
* `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanWitness`
  (`Volume/CVInstantiate.lean:634`) — the Cousins–Vempala hypothesis bundle actually
  quantified over here (rows 9–13) is **jointly satisfiable**.  Degenerate on purpose
  (zero phases), so it witnesses satisfiability and nothing else.  It is *not*
  `Ttc.Box.exists_cvVolAlg_witness` (`Exec/CVBackend.lean:774`): that one witnesses
  `Ttc.cvVolAlg`'s bundle, which carries the equation form of row 12 and is no longer the
  bundle this theorem quantifies over.
* **BLOCKED, and it must stay blocked: there is no full witness for `Ttc.ttc_runtime_mn4`.**
  One would have to inhabit `Ttc.HitAndRunTheorem11Input` (row 8), which is exactly the
  assumed content of Lovász–Vempala Theorem 1.1.  **No witness is faked here.**  The
  witness on the *unconditional* path is `Ttc.ttc_volume_estimate_poly_two_cube`
  (`Exec/TheoremPoly.lean`), at exponential prices.

## Semantic `def`s (`CLAUDE.md` §11)

This file introduces **no `def` into the mathematical development**, and so has no
semantic-`def` surface at all.  (It does contain exactly one `def`:
`private partial def Ttc.Audit.binderProfileAux`, the meta-level binder-counting probe at
the foot of the file.  It is a `Lean.Expr → Nat × Nat × Nat` function used by the
`#binderProfile` command for *reporting*; it asserts nothing, is not `Prop`-valued, and
appears in no statement of this development.)

The one name in the runtime bound that could stand in for a proof —
`Ttc.PolyComplexity.threshFactor` — is **expanded away** in the statement, and
`Ttc.ttc_runtime_mn4_threshFactor` proves the expansion is its definition by `rfl`.  The
remaining names in the bound (`canonRfac`, `toDNFd`, `preprocess`) are *computed from the
input by the algorithm itself*, not claimed identities.

## What is here

| declaration | what it is |
| --- | --- |
| `Ttc.ttc_runtime_mn4_threshFactor` | the threshold factor is the closed form, by `rfl` |
| `Ttc.ttc_runtime_mn4_tol_le_one` | **`heps1`, discharged** at the run's own data |
| `Ttc.ttc_runtime_mn4` | **the goal-state capstone**, 38 residual hypotheses |
| `#binderProfile` | the binder count above, machine-checked rather than asserted |
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Set
open Ttc.Monadic

variable {A : Type*} {n : ℕ}

/-! ## The threshold factor, expanded

`Ttc.PolyComplexity.threshFactor` is the `n`-free part of `Ttc.ttcThresh`'s bound.  The
capstone writes it out rather than naming it, so that no project `def` stands between the
reader and the arithmetic; this lemma is the (definitional) bridge, and its only purpose
is to make "the expansion below is the definition" a *checked* claim rather than a
docstring's word. -/
theorem ttc_runtime_mn4_threshFactor (ε δ : ℝ) (m : ℕ) :
    PolyComplexity.threshFactor ε δ m
      = 41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
          + 15 * (Real.log (15 / (2 * δ)) + Real.log m) + 1 := rfl

/-! ## `heps1`, discharged

The per-cube TV tolerance `ε'/(4·Vol P'ᵢ)` is a legal tolerance — it is at most `1` — at
the run's own data.  This was a binder of `Ttc.ttcPoly_volume_estimate_cv`; it is a
*theorem*, and the capstone below does not carry it.

`Ttc.ttcSampTol_le_one` (`Exec/SampleDischarge.lean:510`) proves exactly this at the run
wrappers' names (`Ttc.ttcAtoms`, `Ttc.ttcInput`, `Ttc.ttcPrec`, `Ttc.ttcSampBody`), which
are `Ttc.algAtoms`, `Ttc.preprocess`, `Ttc.algPrec` and the inflated canonical polytope by
`rfl`; the lemma therefore applies with **no bridging at all**.  Its content is that the
inflated body contains a ball of radius `≥ 64n` (`Ttc.dim_le_ttcSampStep`), hence has
volume `≥ 1` (`Ttc.one_le_ttcSampBody_volume`, `Exec/SampleDischarge.lean:484`), while
`ε' = ε/12 ≤ 1/12`; so the tolerance is at most `1/48`.

Note the direction: this needs a **lower** bound on the inflated body's volume. -/
theorem ttc_runtime_mn4_tol_le_one (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ∀ i : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)},
      (algBlock atoms φ ε δ).epsPrime / (4 *
        (volume (Arlib.KV97.inflated
          (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
          (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
            (latticeScale (algPrec atoms φ ε δ)) i)
          (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
          (canonRfac (toDNFd (preprocess atoms φ))))).toReal) ≤ 1 :=
  fun i => ttcSampTol_le_one atoms φ ε δ hε0 hε1 hn hφ hpos i

/-! ## The capstone -/

set_option maxHeartbeats 1000000 in
/-- **THE GOAL-STATE CAPSTONE: `TTC` at the swapped oracles — accuracy `1 − δ` and
charged cost `≤ m · n⁴ · (explicit factors)`, over ONE run.**

`Ttc.ttcPoly atoms φ ε δ (VolumeAlgorithm.cousinsVempalaOfRunsApproxMean …) …` is
`alg:ttc` with the Cousins–Vempala volume estimator in place of hit-and-miss Monte Carlo
and the hit-and-run law in place of the lazy ball walk.  Both conjuncts speak about **the
same measure**: accuracy about `r.1`, charged cost about `r.2`.

Every residual mathematical input is an explicit, named binder of this statement —
**38 of them**, enumerated in the module docstring's ledger.  In particular
`H : Ttc.HitAndRunTheorem11Input` (Lovász–Vempala Theorem 1.1) and
`hphase_mean`/`hphase_var` (Cousins–Vempala's residual sampler hypotheses) are visible in
the type, inhabited nowhere, and deliberately not hidden behind a structure.

**`hphase_mean` is an interval, not an equation.**  The volume oracle is
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`, not `Ttc.cvVolAlg`: it asks for
`∫ g dν ∈ (1 ± ε/(2(2+ε)m))·(chain(i+1)/chain(i))`, which is what a total-variation bound
on a sampler delivers, rather than the equality
`∫ g dν = chain(i+1)/chain(i)`, which — by
`Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne` — **no** mixing bound
can ever deliver.  Everything else about the run is identical: same coin space
(`Arlib.Probability.NatRunSpace E`), same score, same median selector, same `est`, and
the same `VolumeAlgorithm.correct` guarantee.  The accuracy and cost conclusions below
are unchanged to the character.  `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean_est`
(`Volume/CVInstantiate.lean`) checks by `rfl` that the estimator really is the one
`Ttc.cvVolAlg` builds, so "same run, weaker hypothesis" is a machine-checked claim and not
a docstring's word.

⚠ **This does not prove `TTC` runs in `O(m·n⁴)`.**  The charged cost is one unit per
oracle call (per-call arithmetic, rejection rounds and `alg:ttc` lines 32–42 are priced at
**zero**); this is `Ttc.ttcPoly`, not `Ttc/Model/`'s `Ttc.ttc`; the accuracy conjunct is
conditional on all 38; the warm start is assumed; and the `n⁴` holds only in the
temperature-scale regime `R = O(σ)` (`n⁵` at `R ≍ σ√n`, and
`Arlib.MarkovChains.exists_halfspace_max_lt` shows the obvious repair is **false**).  See
the boxed warning at the head of this file. -/
theorem ttc_runtime_mn4
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    -- **A. the FPRAS parameter range and the input conditions** (ledger 1–7)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    -- **C. the Cousins–Vempala data, and its residual hypotheses** (ledger 9–13)
    (E : Type) [MeasurableSpace E] (ν : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)]
    (phases : Set (Space n) → ℝ → ℝ → ℕ) (σsq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (g : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → ℝ) (B : ℝ)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j) (hg : ∀ K ε p j i, Measurable (g K ε p j i))
    (hgb : ∀ K ε p j i x, |g K ε p j i x| ≤ B)
    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) ∈
        relErr (ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
          (Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
            Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ)))
    (hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + Arlib.GaussianCooling.varBudget (ε / 2) / (phases K ε p : ℝ)) *
            (∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ))) ^ 2)
    -- the run's own sampler data and complexity parameters (data, not hypotheses)
    (rin Rout Mw : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → ℝ)
    (sigma : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Measure (Space n))
    (gam R Mwarm Lc kap cc pf Mcool epsDraw : ℝ)
    -- **B. Lovász–Vempala Theorem 1.1, ASSUMED** (ledger 8)
    (H : HitAndRunTheorem11Input)
    -- **D. the hit-and-run warm start** (ledger 14–22)
    (zin : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Space n)
    (hrin : ∀ i, 0 < rin i)
    (hin : ∀ i, Metric.closedBall (zin i) (rin i) ⊆
      Arlib.KV97.inflated
        (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
        (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
          (latticeScale (algPrec atoms φ ε δ)) i)
        (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))))
    (zout : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Space n)
    (hRout : ∀ i, 0 ≤ Rout i)
    (hout : ∀ i, Arlib.KV97.inflated
        (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
        (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
          (latticeScale (algPrec atoms φ ε δ)) i)
        (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ)))
      ⊆ Metric.closedBall (zout i) (Rout i))
    (hsigma : ∀ i, IsProbabilityMeasure (sigma i))
    (hM : ∀ i, 1 ≤ Mw i)
    (Sx : {c : Cube A // c ∈ toDNFd (preprocess atoms φ)} → Set (Space n))
    (hSm : ∀ i, MeasurableSet (Sx i))
    (hS : ∀ i, sigma i (Sx i) ≤ ENNReal.ofReal
      ((algBlock atoms φ ε δ).epsPrime / (4 *
        (volume (Arlib.KV97.inflated
          (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
          (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
            (latticeScale (algPrec atoms φ ε δ)) i)
          (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
          (canonRfac (toDNFd (preprocess atoms φ))))).toReal) / 2))
    (hdom : ∀ i, ∀ T, MeasurableSet T →
      sigma i (T \ Sx i) ≤ ENNReal.ofReal (Mw i) *
        Arlib.uniformOn volume (Arlib.KV97.inflated
          (canonAm (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ)) i)
          (canonBv (algAtoms atoms φ ε δ) (toDNFd (preprocess atoms φ))
            (latticeScale (algPrec atoms φ ε δ)) i)
          (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
          (canonRfac (toDNFd (preprocess atoms φ)))) (T \ Sx i))
    -- **E. the sampler-side cost regime** (ledger 23–28)
    (hR1 : 1 ≤ R) (hgam0 : 0 < gam) (hgamR : gam ≤ R)
    (hMw1 : 1 ≤ Mwarm) (hMwB : Mwarm ≤ (2 * R) ^ n)
    (hepn : 1 / 2 ^ n ≤ (algBlock atoms φ ε δ).epsPrime)
    -- **F. the volume-side (Gaussian cooling) cost regime** (ledger 29–38)
    (hL : 1 ≤ Lc) (hkap0 : 0 < kap) (hkap1 : kap ≤ 1) (hcc1 : 1 ≤ cc)
    (hcc : cc ≤ 1 + 2 / (n : ℝ)) (hp0 : 0 < pf) (hp1 : pf ≤ 1 / 2)
    (hMc : 1 ≤ Mcool) (hed0 : 0 < epsDraw) (hed1 : epsDraw ≤ 1) :
    -- (accuracy) the estimate is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[r ← ttcPoly atoms φ ε δ
            (VolumeAlgorithm.cousinsVempalaOfRunsApproxMean n E ν phases σsq g B
              hσ hg hgb hphase_mean hphase_var)
            rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) almost every run is charged at most
    -- `m · n⁴ · (2⁴²·(r+1)·log(8M/ε_d²)·(L⁴·log(1/p)/κ³) + 2⁶²·r·(R²/γ²)·log(2R)·Thr)`,
    -- with `Thr` written out as closed arithmetic in `ε`, `δ` and `m`
    (All[r ← ttcPoly atoms φ ε δ
          (VolumeAlgorithm.cousinsVempalaOfRunsApproxMean n E ν phases σsq g B
            hσ hg hgb hphase_mean hphase_var)
          rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
          * (2 ^ 42 * (canonRfac (toDNFd (preprocess atoms φ)) + 1)
                * Real.log (8 * Mcool / epsDraw ^ 2)
                * (Lc ^ 4 * Real.log (1 / pf) / kap ^ 3)
              + 2 ^ 62 * canonRfac (toDNFd (preprocess atoms φ))
                  * (R ^ 2 / gam ^ 2) * Real.log (2 * R)
                  * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                      + 15 * (Real.log (15 / (2 * δ))
                          + Real.log ((toDNFd (preprocess atoms φ)).length))
                      + 1))]) :=
  -- exactly the pair `Ttc.ttcPoly_volume_estimate_cv` assembles (`Exec/PolyAccuracy.lean:849`),
  -- at the approximate-mean constructor instead of `Ttc.cvVolAlg`.  Both halves are generic
  -- in the volume algorithm, so nothing else in the derivation moves.
  ⟨pr_ttcPoly_accuracy_hitAndRun atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
      (VolumeAlgorithm.cousinsVempalaOfRunsApproxMean n E ν phases σsq g B
        hσ hg hgb hphase_mean hphase_var)
      rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw
      H zin hrin hin zout hRout hout
      -- `heps1`, discharged: `Ttc.ttcSampTol_le_one` (see above)
      (ttc_runtime_mn4_tol_le_one atoms φ ε δ hε0 hε1 hn hφ hpos)
      hsigma hM Sx hSm hS hdom,
    all_ttcPoly_cost_le_quartic atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
      (VolumeAlgorithm.cousinsVempalaOfRunsApproxMean n E ν phases σsq g B
        hσ hg hgb hphase_mean hphase_var)
      rin Rout Mw sigma gam R Mwarm Lc kap cc pf Mcool epsDraw
      -- `hrfac`, discharged: `Ttc.one_le_canonRfac_preprocess`
      (one_le_canonRfac_preprocess atoms φ ε hε0 hε1 hn hφ hpos)
      hR1 hgam0 hgamR hMw1 hMwB
      -- `hep0`, `hep1`, discharged: both unconditional
      (algBlock_epsPrime_pos atoms φ ε δ) (algBlock_epsPrime_le_one atoms φ ε δ) hepn
      hL hkap0 hkap1 hcc1 hcc hp0 hp1 hMc hed0 hed1⟩

end Ttc

/-! ## The binder profile, machine-checked (`CLAUDE.md` §11)

The ledger's counts are asserted in a docstring, which `#print axioms` cannot see.  This
command makes them checkable: it walks the declaration's raw type and reports the number
of top-level `∀`-binders split by `BinderInfo`, which is exactly the
"raw = explicit + implicit + instance" convention of `Ttc/Exec/Endgoal.lean:64-70`.  It
asserts nothing and is used for reporting only. -/

open Lean in
/-- Count a type's top-level `∀`-binders as `(explicit, implicit, instance)`. -/
private partial def Ttc.Audit.binderProfileAux : Expr → Nat × Nat × Nat
  | .forallE _ _ b bi =>
      let (e, i, s) := Ttc.Audit.binderProfileAux b
      match bi with
      | .default => (e + 1, i, s)
      | .implicit => (e, i + 1, s)
      | .strictImplicit => (e, i + 1, s)
      | .instImplicit => (e, i, s + 1)
  | _ => (0, 0, 0)

open Lean Elab Command in
/-- `#binderProfile Foo` prints `Foo`'s top-level binder counts. -/
elab "#binderProfile " id:ident : command => do
  let env ← getEnv
  let c ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  let some ci := env.find? c | throwError "not found: {c}"
  let (e, i, s) := Ttc.Audit.binderProfileAux ci.type
  logInfo m!"{c}: {e + i + s} raw ∀-binders = {e} explicit + {i} implicit + \
    {s} instance"

#binderProfile Ttc.ttc_runtime_mn4
#binderProfile Ttc.ttcPoly_volume_estimate_cv

/-! ## Axiom profile (`CLAUDE.md` §4) -/

#print axioms Ttc.ttc_runtime_mn4_threshFactor
#print axioms Ttc.ttc_runtime_mn4_tol_le_one
#print axioms Ttc.ttc_runtime_mn4
