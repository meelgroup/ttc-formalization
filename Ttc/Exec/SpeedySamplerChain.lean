/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Sampler.SpeedyBackendUncond
import Ttc.Exec.SampPricePoly

/-!
# One step count that both mixes and is polynomially priced

Four results landed separately and were never composed:

* **(A)** `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_uncond`
  (`Ttc/Sampler/SpeedyBackendUncond.lean:181`) — for measurable convex `K ⊆ ℝⁿ` with
  `Metric.ball cen γ ⊆ K` and all pairwise distances at most `Dm`, the lazy speedy walk
  started at `Arlib.uniformOn volume (Metric.ball cen γ)` is within total variation `ρ` of
  `Arlib.uniformOn volume K` after `Ttc.speedyMixSteps n (Dm/γ) ρ` steps.  No `hequiv`, no
  isoperimetry, no warmness.
* **(B)** `Ttc.SamplerCost.drawOpCharge_le_poly` (`Ttc/Exec/SampPricePoly.lean:303`) —
  `drawOpCharge t n rfac ≤ 2³⁰·n⁶·rfac·(Dm/γ)²·(log(1+Dm/γ)+log(2/ρ))/ρ²`, for any `t`
  bounded by the speedy walk's closed-form step count.
* **(C)** `Ttc.exp_mul_log_le_mixSteps` (`Ttc/Sampler/SpeedyBackend.lean:344`) —
  `2048·4ⁿ·log(√Mw/eps) ≤ Ttc.mixSteps n γ Dm δ Mw eps`, the *exponential* lower bound on
  the ball-walk step count TTC's price is built from.
* **(D)** `Ttc.SamplerCost.samplePrice_eq_drawOpCharge` — `samplePrice` **is**
  `drawOpCharge` at the hit-and-run count, by `rfl`, so (B) prices `samplePrice` verbatim
  once a backend substitutes its own `t`.

This file is the composition.  It adds no definition; every declaration is a `theorem`.

## The bridge, and the footgun it avoids

(B)'s hypothesis is `t ≤ closed-form`, where the closed form is *verbatim* the step count
of `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps`.  (A)'s step
count is `Ttc.speedyMixSteps`, i.e. `Arlib.MarkovChains.conductanceMixingTime` at the same
warmness and conductance.  These are **not** the same number: the closed form is
`conductanceMixingTime`'s *bound*, not its value.

`Ttc.speedyMixSteps_le_closedForm` (§1) proves `speedyMixSteps ≤ closed-form` directly from
`Arlib.MarkovChains.conductanceMixingTime_le`, with no slack introduced.  That is what lets
**one and the same `t := Ttc.speedyMixSteps n (Dm/γ) ρ`** appear in both conjuncts of §2.

⚠ Taking `t := ⌈closed-form⌉₊` instead would satisfy (A) — any `m ≥ speedyMixSteps` does —
but would **break** (B), whose hypothesis is an upper bound on `t`.  The direction of the
inequality is the whole trap.  Use `Ttc.speedyMixSteps` itself, as §2 and §5 do.

## What §2 says

`Ttc.speedyWalk_mixes_and_drawPrice_le_poly`: at `t := Ttc.speedyMixSteps n (Dm/γ) ρ`, the
walk **reaches TV `ρ`** *and* the charged price of one draw at that same `t` is at most
`2³⁰·n⁶·rfac·(Dm/γ)²·(log(1+Dm/γ)+log(2/ρ))/ρ²` — polynomial in `n`, with every suppressed
factor printed.  A reader sees one step count buying both.

`hγD : 2γ ≤ Dm` is a named binder rather than a derived fact.  It is forced by the geometry
(a body containing a ball of radius `γ` has diameter at least `2γ`), but the sharp form
needs a limiting argument and no lemma in the repository provides it — only the cheap
`Arlib.MarkovChains.half_le_diam_bound_of_ball_subset` (`1/2 ≤ D`) exists.  (B) binds
`2γ ≤ Dm` too, so nothing is weakened by naming it here.

## §3–§4: the comparison, and the honest threshold

Two different exponentials are available to compare against, and they are **not**
interchangeable:

* `Ttc.mixStepsBound` — the closed form TTC's *charged price* is the ceiling of
  (`Ttc.ttcSampPrice = ⌈Ttc.ttcSampStepsPrice⌉₊`, and `ttcSampStepsPrice = mixStepsBound`
  by `rfl`).  It carries `4ⁿ·n²·(Dm/dl)²·((γ+Dm)/γ)^{4n}`.
* `Ttc.mixSteps` — the ball walk's *own* step count, of which (C) gives the much weaker
  lower bound `2048·4ⁿ·log(√Mw/eps)`: no `n²`, no `((γ+Dm)/γ)^{4n}`.

Hence two different thresholds, and both are stated:

| route | geometry | threshold proved here |
| --- | --- | --- |
| `mixStepsBound` | `γ=1, Dm=2, dl=1, Mw=2, eps=1/2, ρ=rfac=1` | `n = 3` (`n = 2` is **false**) |
| `mixSteps` (C) | `Dm = 4γ`, `ρ = eps = 1/2`, `Mw = 1`, `rfac = 1` | `n = 29` |

**The `n = 2` claim, verified rather than repeated.**  `Ttc/Exec/SampPricePoly.lean`'s
docstring asserts in prose, without machine-checking it, that at `n = 2` the comparison
behind `Ttc.SamplerCost.drawOpCharge_le_mixStepsBound_at_dim_sixteen` fails, quoting
`≈4.9·10¹¹` against `≈5.7·10¹⁰`.  `Ttc.expTerm_lt_polyPrice_at_dim_two` (§3) is that claim
**proved**: at `n = 2` the two sides are `2³⁸·(log 3 + log 2) ≈ 4.925·10¹¹` and
`3·log 2·2²²·3⁸ ≈ 5.723·10¹⁰`, and the polynomial side is **strictly larger**.  The claim
is confirmed exactly as stated.

⚠ **Read `Ttc.expTerm_lt_polyPrice_at_dim_two` for what it is.**  It refutes the
*intermediate bound comparison* — the proof route `..._at_dim_sixteen` uses — at `n = 2`.
It does **not** say `drawOpCharge t 2 1 > mixStepsBound 2 1 2 1 2 (1/2)`; that endpoint
inequality is left undetermined here, and for small `t` it may well hold.  What is refuted
is the route, not the conclusion.

`Ttc.polyPrice_le_expTerm_at_dim_three` and `Ttc.drawOpCharge_le_mixStepsBound_at_dim_three`
are the honest threshold on that route: `n = 3`, not `n = 16`.  On the (C) route the same
argument lands at `n = 29`; `n = 28` fails under the `log 5 ≤ 3·log 2` relaxation used, and
neither `3` nor `29` is claimed to be the minimum over all proofs — they are where *these*
proofs land.  The gap `3 → 29` is entirely the `n²·((γ+Dm)/γ)^{4n}` that (C)'s lower bound
throws away.

**Unit mismatch, stated.**  On the left is an *operation* count
`drawOpCharge t n rfac = (t+2)·⌈n·rfac⌉₊`; on the right a bare *step* count.  Comparing
them is conservative in the ball walk's favour (the ball walk is charged nothing per step),
and it is the same convention `..._at_dim_sixteen` already uses.

## What is NOT closed — the chain to `Ttc.ttcSampPrice` at TTC's own arguments

`Ttc.SamplerCost.mixStepsBound_le_ttcSampPrice` terminates the exponential side at the real
price object, but only at TTC's own arguments `ttcSampInradius`, `ttcSampDiamPrice`,
`ttcSampStep`, `ttcSampWarmPrice`, `ttcSampTolPrice`.  **This file does not close
`poly ≤ ttcSampPrice` there, and does not claim to.**  Four concrete blockers:

1. `2·ttcSampInradius ≤ ttcSampDiamPrice` does not exist.  Only
   `Ttc.ttcSampInradius_le_ttcSampDiamPrice` (`Exec/SampPriceHR:149`) — the factor `2` that
   (B)'s `hγD` needs is not available.
2. `ttcSampTolPrice ≤ 1` does not exist.  Only `Ttc.ttcSampTolPrice_pos`
   (`Exec/InflateBound:646`); `Ttc.ttcSampTol_le_one` (`Exec/SampleDischarge:510`) is about
   the *per-cube* `ttcSampTol` and reaching it needs a cube of the DNF, i.e. a further
   nonemptiness hypothesis.  `Ttc.SamplerCost.expTerm_le_mixStepsBound` binds `eps ≤ 1`.
3. `rfac` — the facet count `Ttc.canonRfac` — appears on the polynomial side with **no**
   counterpart on the exponential side and no upper bound anywhere.
4. There is no uniform dimension threshold at symbolic arguments, and there cannot be one.
   The polynomial side carries `1/ρ²` where the exponential side carries only
   `log(1/eps)`; identifying the two accuracies (`ρ := eps`) makes the ratio diverge as
   `eps → 0` at fixed `n`.  §3's `n = 2` refutation is one instance of the same
   obstruction: the comparison is genuinely conditional on the dimension *and* the
   geometry, so no unconditional symbolic form exists to prove.

A conditional variant that simply hypothesises the numeric comparison is not offered: it
would assume what it purports to establish.

## Scope — this does **not** make TTC polynomial-time

Nothing here is a running time, and no theorem below bounds one.

* `Ttc.stepCost` counts oracle calls; the arithmetic **inside** a call or a step is priced
  at **zero** (`Ttc/CostModel.lean:87-91`).  A bound on an undercount is not a bound on the
  count.
* `Ttc.VolumeAlgorithm` (`Ttc/Volume/Oracle.lean:70`) has **no complexity field** — its
  fields are `Ω`, `mΩ`, `μ`, `isProb`, `est` and the accuracy guard.  There is no runtime
  in the model to bound in the first place.
* The sampler's rounding/rejection stage is **uncosted**: `Ttc.kv97SampD` is a density,
  consumes no coin sequence, and no coin-consuming object performing the rejection loop
  exists in this development (`Ttc/CostModel.lean:84`).  Its rounds are unbounded.
* The volume oracle is **independently exponential**: `Ttc.MonteCarlo.nSamp` scales as the
  inverse hit probability, and `Ttc.ttcVolPrice` inherits that.  Making the *sampler* cheap
  does not make the pipeline cheap.
* `Ttc.ttc` is **charged prices it does not run**: `Ttc/Exec/PricedHeadline.lean:18-50`
  fixes the Cousins–Vempala volume price and the hit-and-run sampling price, while the
  modelled run's oracle bundle is `Ttc.mcVol` with a lazy-ball-walk sampling law.  Fixing
  those two numerals is arithmetic in `Ttc.runCost`'s fold, not a costing of the run.
* `Ttc.mixSteps` prices the chain the sampler's *law* is defined by, not steps the modelled
  run takes (`Ttc/Exec/SamplePrice.lean:77-80`).

**Nothing in `Ttc/` is rewired by this file.**  No existing declaration is edited, no
backend is replaced, `Ttc.HitAndRunTheorem11Input` is still the assumed contract the
pipeline consumes, and `Ttc.ttcSampPrice` is unchanged and still exponential.  This file
adds theorems that sit beside the pipeline; it does not enter it.

## Declarations

No `def`, `structure`, `class`, `axiom`, `sorry`, `admit` or `native_decide` occurs below.
The step count is the existing `Ttc.speedyMixSteps`, whose meaning is pinned by
`Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_at_steps` in `SpeedyBackend.lean`; the price is
the existing `Ttc.SamplerCost.drawOpCharge`, whose modelling caveat
(`Ttc/Exec/SamplerCost.lean:360-362` — no executable step is measured by it) is inherited
unchanged.
-/

namespace Ttc

open MeasureTheory
open scoped ENNReal

set_option maxRecDepth 100000

/-! ## 1. The bridge: `Ttc.speedyMixSteps` discharges the price theorem's hypothesis -/

/-- **`Ttc.speedyMixSteps` satisfies the step-count hypothesis of
`Ttc.SamplerCost.drawOpCharge_le_poly`, exactly.**

```
speedyMixSteps n D ρ  ≤  (2n·log(1+D) + 2·log(2/ρ)) / (min (1/32) (1/(8D)·(ρ/(4n))/(256n)))² + 1
```

The right-hand side is character-for-character `drawOpCharge_le_poly`'s `ht` at `D := Dm/γ`,
and the proof is `Arlib.MarkovChains.conductanceMixingTime_le` at
`M = (1+D)^{2n}`, `φ = min(1/32, (1/(8D))·(ρ/(4n))/(256n))`, `eps = ρ/2` — the very
instance `Ttc.speedyMixSteps` is *defined* to be, so the `rfl` at the end closes the gap
with **no slack introduced**.

This is the lemma that makes the composition legal.  `Ttc.speedyMixSteps_le`
(`SpeedyBackend.lean:256`) is *not* usable in its place: it weakens `φ⁻²` to
`1024 + (8192·D·n²/ρ)²` first, and the price theorem's hypothesis is stated at the
un-weakened `min`.

⚠ The hypothesis being discharged is an **upper** bound on `t`.  A larger step count — e.g.
`⌈closed-form⌉₊`, which still satisfies the mixing theorem, whose `hm` is a *lower* bound —
does **not** satisfy it.  See the module docstring. -/
theorem speedyMixSteps_le_closedForm (n : ℕ) {D rho : ℝ} (hn : 1 ≤ n) (hD : (1 : ℝ) / 2 ≤ D)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    (speedyMixSteps n D rho : ℝ)
      ≤ (2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho))
          / (min (1 / 32 : ℝ)
              (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2 + 1 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hD0 : (0 : ℝ) < D := by linarith
  have hM : (1 : ℝ) ≤ (1 + D) ^ (2 * n) := one_le_pow₀ (by linarith)
  have hc0 : (0 : ℝ) < 1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)) := by positivity
  have hphi0 : (0 : ℝ) < min (1 / 32)
      (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))) := lt_min (by norm_num) hc0
  have heps : (0 : ℝ) < rho / 2 := by linarith
  have hsqrt : rho / 2 ≤ Real.sqrt ((1 + D) ^ (2 * n)) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt ((1 + D) ^ (2 * n)) := by
      have h2 := Real.sqrt_le_sqrt hM
      rwa [Real.sqrt_one] at h2
    linarith
  have hlogM : Real.log ((1 + D) ^ (2 * n)) = 2 * (n : ℝ) * Real.log (1 + D) := by
    rw [Real.log_pow]; push_cast; ring
  have hlogeps : Real.log (1 / (rho / 2)) = Real.log (2 / rho) := by rw [one_div_div]
  have hle := Arlib.MarkovChains.conductanceMixingTime_le (M := (1 + D) ^ (2 * n))
    (phi := min (1 / 32) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))))
    (eps := rho / 2) hM hphi0 heps hsqrt
  rw [hlogM, hlogeps] at hle
  have hdef : speedyMixSteps n D rho
      = Arlib.MarkovChains.conductanceMixingTime ((1 + D) ^ (2 * n))
          (min (1 / 32) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) (rho / 2) :=
    rfl
  rw [hdef]
  exact hle

/-! ## 2. THE COMPOSED THEOREM -/

/-- **THE COMPOSED THEOREM: the same step count mixes *and* is polynomially priced.**

For a measurable convex body `K ⊆ ℝⁿ` (`2 ≤ n`) with an inscribed ball
`Metric.ball cen γ ⊆ K` at *any* centre and *any* positive radius, all pairwise distances
at most `Dm`, and `2γ ≤ Dm`, at the **single** step count
`t := Ttc.speedyMixSteps n (Dm/γ) ρ`:

1. the lazy speedy walk with step `γ·ρ/(4n)`, started from
   `Arlib.uniformOn volume (Metric.ball cen γ)`, is within total variation `ρ` of
   `Arlib.uniformOn volume K` after `t` steps — this is
   `Ttc.tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_uncond` at `m := t`; **and**
2. the charged price of one draw at that same `t` is at most
   `2³⁰·n⁶·rfac·(Dm/γ)²·(log(1+Dm/γ) + log(2/ρ))/ρ²` — this is
   `Ttc.SamplerCost.drawOpCharge_le_poly`, whose step-count hypothesis is discharged by
   `Ttc.speedyMixSteps_le_closedForm`.

`t` occurs **syntactically identically** in the two conjuncts.  That is the point: a reader
does not have to check that the count that mixes is the count that is priced.

Every hypothesis is named and nothing is suppressed: `hn : 2 ≤ n` (the mixing theorem's own
scope limit, inherited from `Arlib.hiso_ellProb_of_ball_bound`); `hγ0`, `hball`, `hD`,
`hγD : 2γ ≤ Dm` (the geometry — `(Dm/γ)²` is **printed**, not absorbed); `hrho0`, `hrho1`
(the TV accuracy — `log(2/ρ)` and `1/ρ²` are **printed**); `hrfac : 1 ≤ rfac` (the facet
count, charged at `⌈n·rfac⌉₊` per step, not suppressed).

⚠ Conjunct 2 is a **charge in a cost model**, not a running time.  See the module
docstring's scope section, and `Ttc/Exec/SamplerCost.lean:360-362`: no executable step is
measured by `Ttc.SamplerCost.stepOpCharge`. -/
theorem speedyWalk_mixes_and_drawPrice_le_poly {n : ℕ} (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    {cen : EuclideanSpace ℝ (Fin n)} {γ : ℝ} (hγ0 : 0 < γ) (hball : Metric.ball cen γ ⊆ K)
    {Dm : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ Dm) (hγD : 2 * γ ≤ Dm)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) {rfac : ℝ} (hrfac : 1 ≤ rfac) :
    Arlib.TVLe
        (Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy
            (Arlib.MarkovChains.speedyWalk K (γ * (rho / (4 * (n : ℝ))))))
          (Arlib.uniformOn volume (Metric.ball cen γ))
          (speedyMixSteps n (Dm / γ) rho))
        (Arlib.uniformOn volume K) (ENNReal.ofReal rho)
      ∧ (SamplerCost.drawOpCharge (speedyMixSteps n (Dm / γ) rho) n rfac : ℝ)
          ≤ 2 ^ 30 * (n : ℝ) ^ 6 * rfac * (Dm / γ) ^ 2
              * (Real.log (1 + Dm / γ) + Real.log (2 / rho)) / rho ^ 2 := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hDg : (2 : ℝ) ≤ Dm / γ := by
    rw [le_div_iff₀ hγ0]; linarith
  refine ⟨tvLe_iterate_lazy_speedyWalk_uniformOn_of_inscribed_uncond hn hKm hKc hγ0 hball hD
    hrho0 hrho1 le_rfl, ?_⟩
  exact SamplerCost.drawOpCharge_le_poly n hn hrfac hγ0 hγD hrho0 hrho1
    (speedyMixSteps_le_closedForm n hn1 (by linarith) hrho0 hrho1)

/-! ## 3. The `Ttc.mixStepsBound` route: `n = 2` is FALSE, `n = 3` is the honest threshold -/

/-- **The `n = 2` claim of `Ttc/Exec/SampPricePoly.lean`'s docstring, machine-checked.**

That docstring says, in prose and explicitly *not* machine-checked, that the comparison
behind `Ttc.SamplerCost.drawOpCharge_le_mixStepsBound_at_dim_sixteen` is **false** at
`n = 2`, quoting `≈4.9·10¹¹` against `≈5.7·10¹⁰`.  This is that claim, proved.

The two sides are the two sides of `Ttc.SamplerCost.polyPrice_le_expTerm_at_dim_sixteen`
with `16` replaced by `2` throughout — same geometry `γ = 1`, `Dm = 2`, `dl = 1`, `Mw = 2`,
`eps = 1/2`, `ρ = rfac = 1`.  They collapse to

* polynomial side `= 2³⁰·2⁶·4·(log 3 + log 2) = 274877906944·(log 3 + log 2) ≈ 4.925·10¹¹`;
* exponential side `= 3·log 2·(16384·4²·2²·2²·3⁸) = 82556485632·log 2 ≈ 5.723·10¹⁰`,

and the inequality goes the **wrong way**: it reduces to `2·log 2 > 0.3·log 2`, since
`log 3 ≥ log 2 > 0`.  The margin is a factor of about `8.6`.  The sibling agent's two
numbers are confirmed exactly.

⚠ **What this does and does not refute.**  It refutes the *intermediate bound comparison*
— the route `..._at_dim_sixteen` takes — at `n = 2`.  It says **nothing** about the
endpoint inequality `drawOpCharge t 2 1 ≤ mixStepsBound 2 1 2 1 2 (1/2)`, which is left
undetermined here and may well hold for small `t` (`drawOpCharge` is `(t+2)·⌈n·rfac⌉₊`,
which is small when `t` is).  Do not read this theorem as
`drawOpCharge > mixStepsBound`. -/
theorem expTerm_lt_polyPrice_at_dim_two :
    (Real.log 2 + 2 * Real.log (1 / (1 / 2 : ℝ)))
        * (16384 * 4 ^ (2 : ℕ) * ((2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ 2 / (1 : ℝ) ^ 2
            * (((1 : ℝ) + 2) / 1) ^ (4 * (2 : ℕ)))
      < 2 ^ 30 * ((2 : ℕ) : ℝ) ^ 6 * 1 * ((2 : ℝ) / 1) ^ 2
          * (Real.log (1 + (2 : ℝ) / 1) + Real.log (2 / (1 : ℝ))) / (1 : ℝ) ^ 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog3 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hinv : Real.log (1 / (1 / 2 : ℝ)) = Real.log 2 := by norm_num
  rw [hinv]
  have hlhs : 2 ^ 30 * ((2 : ℕ) : ℝ) ^ 6 * 1 * ((2 : ℝ) / 1) ^ 2
      * (Real.log (1 + (2 : ℝ) / 1) + Real.log (2 / (1 : ℝ))) / (1 : ℝ) ^ 2
      = 274877906944 * (Real.log 3 + Real.log 2) := by
    norm_num
  have hrhs : (Real.log 2 + 2 * Real.log 2)
      * (16384 * 4 ^ (2 : ℕ) * ((2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ 2 / (1 : ℝ) ^ 2
          * (((1 : ℝ) + 2) / 1) ^ (4 * (2 : ℕ)))
      = 82556485632 * Real.log 2 := by
    norm_num
    ring
  rw [hlhs, hrhs]
  linarith

/-- **The same comparison at `n = 3` is true — the honest threshold on this route.**

`Ttc.SamplerCost.polyPrice_le_expTerm_at_dim_sixteen` with `16` replaced by `3`:

* polynomial side `= 2³⁰·3⁶·4·(log 3 + log 2) = 3131031158784·(log 3 + log 2)`;
* exponential side `= 3·log 2·(16384·4³·3²·2²·3¹²) = 60183678025728·log 2`,

and `log 3 + log 2 ≤ 3·log 2` (because `3 ≤ 4 = 2²`) reduces it to
`3131031158784·3 ≤ 60183678025728`, i.e. `9.393·10¹² ≤ 6.018·10¹³`.

So the `n = 16` of `Ttc/Exec/SampPricePoly.lean` was not the threshold; `3` is where this
route lands.  It is **not** claimed to be minimal over all proofs — only that `n = 2` is
false (`Ttc.expTerm_lt_polyPrice_at_dim_two`) and `n = 3` is proved, which pins the
threshold for *this* argument exactly. -/
theorem polyPrice_le_expTerm_at_dim_three :
    2 ^ 30 * ((3 : ℕ) : ℝ) ^ 6 * 1 * ((2 : ℝ) / 1) ^ 2
        * (Real.log (1 + (2 : ℝ) / 1) + Real.log (2 / (1 : ℝ))) / (1 : ℝ) ^ 2
      ≤ (Real.log 2 + 2 * Real.log (1 / (1 / 2 : ℝ)))
          * (16384 * 4 ^ (3 : ℕ) * ((3 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ 2 / (1 : ℝ) ^ 2
              * (((1 : ℝ) + 2) / 1) ^ (4 * (3 : ℕ))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have h1 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hinv : Real.log (1 / (1 / 2 : ℝ)) = Real.log 2 := by norm_num
  rw [hinv]
  have hlhs : 2 ^ 30 * ((3 : ℕ) : ℝ) ^ 6 * 1 * ((2 : ℝ) / 1) ^ 2
      * (Real.log (1 + (2 : ℝ) / 1) + Real.log (2 / (1 : ℝ))) / (1 : ℝ) ^ 2
      = 3131031158784 * (Real.log 3 + Real.log 2) := by
    norm_num
  have hrhs : (Real.log 2 + 2 * Real.log 2)
      * (16384 * 4 ^ (3 : ℕ) * ((3 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ 2 / (1 : ℝ) ^ 2
          * (((1 : ℝ) + 2) / 1) ^ (4 * (3 : ℕ)))
      = 60183678025728 * Real.log 2 := by
    norm_num
    ring
  rw [hlhs, hrhs]
  linarith

/-- **The whole polynomial draw price is below the exponential step count, at `n = 3`.**

`Ttc.SamplerCost.drawOpCharge_le_mixStepsBound_at_dim_sixteen` at the threshold dimension:

```
drawOpCharge t 3 1 ≤ mixStepsBound 3 1 2 1 2 (1/2)
```

for every `t` the speedy walk's closed-form count admits — in particular for
`t = Ttc.speedyMixSteps 3 (2/1) 1`, which is
`Ttc.drawOpCharge_speedyMixSteps_le_mixStepsBound_dim3` in §5.

`Ttc.mixStepsBound` at these arguments is the closed form `Ttc.ttcSampPrice` is the
`Nat.ceil` of (`Ttc.SamplerCost.mixStepsBound_le_ttcSampPrice`), but **at TTC's own
arguments, not at these numerals** — see the module docstring for why that chain does not
close.

⚠ Left side is an operation count `(t+2)·⌈n·rfac⌉₊`; right side a bare step count. -/
theorem drawOpCharge_le_mixStepsBound_at_dim_three {t : ℕ}
    (ht : (t : ℝ)
      ≤ (2 * ((3 : ℕ) : ℝ) * Real.log (1 + (2 : ℝ) / 1) + 2 * Real.log (2 / (1 : ℝ)))
          / (min (1 / 32 : ℝ)
              (1 / (8 * ((2 : ℝ) / 1)) * ((1 : ℝ) / (4 * ((3 : ℕ) : ℝ)))
                / (256 * ((3 : ℕ) : ℝ)))) ^ 2 + 1) :
    (SamplerCost.drawOpCharge t 3 1 : ℝ) ≤ mixStepsBound 3 1 2 1 2 (1 / 2) := by
  have h1 := SamplerCost.drawOpCharge_le_poly (n := 3) (γ := 1) (Dm := 2) (rho := 1)
    (rfac := 1) (t := t) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
    le_rfl ht
  have h2 := SamplerCost.expTerm_le_mixStepsBound (n := 3) (γ := 1) (Dm := 2) (dl := 1)
    (Mw := 2) (eps := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := polyPrice_le_expTerm_at_dim_three
  linarith

/-! ## 4. The comparison against `Ttc.mixSteps` itself, via (C) -/

/-- **The numeric core of the `n = 29` comparison against the ball walk's own step count.**

Left: the polynomial price bound of `Ttc.SamplerCost.drawOpCharge_le_poly` at `n = 29`,
`Dm/γ = 4`, `ρ = 1/2`, `rfac = 1`.  Right: the exponential lower bound of
`Ttc.exp_mul_log_le_mixSteps` at `n = 29`, `Mw = 1`, `eps = 1/2`.

`log 5 + log 4 ≤ 5·log 2` (from `5 ≤ 8 = 2³` and `4 = 2²`) reduces it to the numeral
inequality `2³⁰·29⁶·4²/(1/2)²·5 ≤ 2048·4²⁹`, i.e.
`204379736847448801280 ≤ 590295810358705651712 = 2⁶⁹`, a factor of about `2.9`.

`n = 28` fails under that relaxation.  `29` is where **this** proof lands; no minimality is
claimed. -/
theorem polyPrice_le_expLowerBound_at_dim_29 :
    2 ^ 30 * ((29 : ℕ) : ℝ) ^ 6 * 1 * ((4 : ℝ)) ^ 2
        * (Real.log (1 + (4 : ℝ)) + Real.log (2 / (1 / 2 : ℝ))) / (1 / 2 : ℝ) ^ 2
      ≤ 2048 * 4 ^ (29 : ℕ) * Real.log (Real.sqrt 1 / (1 / 2 : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  have h5 : Real.log (5 : ℝ) ≤ 3 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 5) (by norm_num : (5:ℝ) ≤ 8)
    linarith
  have hs : Real.log (Real.sqrt 1 / (1 / 2 : ℝ)) = Real.log 2 := by
    rw [Real.sqrt_one]
    norm_num
  have hl : Real.log (1 + (4 : ℝ)) = Real.log 5 := by norm_num
  have he : Real.log (2 / (1 / 2 : ℝ)) = Real.log 4 := by norm_num
  rw [hs, hl, he]
  have hsum : Real.log 5 + Real.log 4 ≤ 5 * Real.log 2 := by
    rw [h4]; linarith
  have hcoef : (0 : ℝ) ≤ 2 ^ 30 * ((29 : ℕ) : ℝ) ^ 6 * 1 * ((4 : ℝ)) ^ 2 / (1 / 2 : ℝ) ^ 2 := by
    positivity
  have hrw : 2 ^ 30 * ((29 : ℕ) : ℝ) ^ 6 * 1 * ((4 : ℝ)) ^ 2
        * (Real.log 5 + Real.log 4) / (1 / 2 : ℝ) ^ 2
      = (2 ^ 30 * ((29 : ℕ) : ℝ) ^ 6 * 1 * ((4 : ℝ)) ^ 2 / (1 / 2 : ℝ) ^ 2)
          * (Real.log 5 + Real.log 4) := by ring
  rw [hrw]
  have hstep1 : (2 ^ 30 * ((29 : ℕ) : ℝ) ^ 6 * 1 * ((4 : ℝ)) ^ 2 / (1 / 2 : ℝ) ^ 2)
        * (Real.log 5 + Real.log 4)
      ≤ (2 ^ 30 * ((29 : ℕ) : ℝ) ^ 6 * 1 * ((4 : ℝ)) ^ 2 / (1 / 2 : ℝ) ^ 2)
          * (5 * Real.log 2) :=
    mul_le_mul_of_nonneg_left hsum hcoef
  have hnum : (2 : ℝ) ^ 30 * ((29 : ℕ) : ℝ) ^ 6 * 1 * ((4 : ℝ)) ^ 2 / (1 / 2 : ℝ) ^ 2 * 5
      ≤ 2048 * 4 ^ (29 : ℕ) := by
    norm_num
  have hstep2 := mul_le_mul_of_nonneg_right hnum hlog2.le
  linarith

/-- **The speedy draw price is below the ball walk's own step count, at `n = 29`.**

```
drawOpCharge t 29 1 ≤ mixSteps 29 γ Dm δ 1 (1/2)        whenever Dm = 4γ, 0 < γ, 0 < δ
```

for every `t` the speedy walk's closed-form count at `Dm/γ` and `ρ = 1/2` admits — in
particular for `t = Ttc.speedyMixSteps 29 (Dm/γ) (1/2)`.

Unlike §3 this compares against `Ttc.mixSteps`, the ball walk's **own** step count, through
`Ttc.exp_mul_log_le_mixSteps`.  The right-hand side is therefore the honest object; the
price of that honesty is the threshold, `29` instead of `3`, because (C)'s lower bound
`2048·4ⁿ·log(√Mw/eps)` discards the `n²·((γ+Dm)/γ)^{4n}` that `Ttc.mixStepsBound` carries.

The geometry is left free apart from the aspect ratio `Dm = 4γ`, so the theorem applies at
`γ ≠ 1` and a nonzero centre — see §5.  Warmness is taken at `Mw = 1`, the value **most
favourable to the ball walk** (a perfectly warm start), and both accuracies are `1/2`, so
the two sides are compared at the same tolerance.  `(C)` is non-trivial exactly when
`eps < √Mw`, which `1/2 < 1` satisfies.

⚠ Left side is an operation count `(t+2)·⌈29·1⌉₊ = 29(t+2)`; right side a bare step count,
charged nothing per step. -/
theorem drawOpCharge_le_mixSteps_at_dim_29 {γ Dm δ : ℝ} (hγ0 : 0 < γ) (hDm : Dm = 4 * γ)
    (hδ : 0 < δ) {t : ℕ}
    (ht : (t : ℝ)
      ≤ (2 * ((29 : ℕ) : ℝ) * Real.log (1 + Dm / γ) + 2 * Real.log (2 / (1 / 2 : ℝ)))
          / (min (1 / 32 : ℝ)
              (1 / (8 * (Dm / γ)) * ((1 / 2 : ℝ) / (4 * ((29 : ℕ) : ℝ)))
                / (256 * ((29 : ℕ) : ℝ)))) ^ 2 + 1) :
    (SamplerCost.drawOpCharge t 29 1 : ℝ) ≤ mixSteps 29 γ Dm δ 1 (1 / 2) := by
  have hratio : Dm / γ = 4 := by
    rw [hDm]; field_simp
  have h1 := SamplerCost.drawOpCharge_le_poly (n := 29) (γ := γ) (Dm := Dm) (rho := 1 / 2)
    (rfac := 1) (t := t) (by norm_num) le_rfl hγ0 (by rw [hDm]; linarith) (by norm_num)
    (by norm_num) ht
  rw [hratio] at h1
  have h2 := exp_mul_log_le_mixSteps (n := 29) (γ := γ) (Dm := Dm) (δ := δ) (Mw := 1)
    (eps := 1 / 2) (by norm_num) hγ0 (by rw [hDm]; linarith) hδ le_rfl (by norm_num)
    (by norm_num)
  have h3 := polyPrice_le_expLowerBound_at_dim_29
  linarith

/-! ## 5. Non-vacuity witnesses (`CLAUDE.md` §11)

Every theorem above is an implication, so each needs a satisfiable antecedent.  The two
below discharge the step-count hypothesis with `Ttc.speedyMixSteps` itself — the whole
point of §1 — rather than with an unexplained numeral.

| witness | discharges | leaves open |
| --- | --- | --- |
| `..._le_mixStepsBound_dim3` | §3's `ht`, at `t := speedyMixSteps 3 (2/1) 1` | — |
| `speedy_mixes_and_beats_ballWalk_dim29` | **everything**, at `γ = 1/2`, `cen = 3·e₀` | — |

The second has **no hypotheses at all**, mixes at a *non-vacuous* tolerance `ρ = 1/2`
(`ENNReal.ofReal 1` is the vacuous total-variation bound), uses a chart
`y ↦ 3e₀ + (1/2)·y` that is neither translation-free nor scaling-free, starts from a law
whose support is a *strict* subset of the body, and prices at a **positive** natural.  What
is *not* claimed, exactly as in `SpeedyBackendUncond.lean`: that the `t`-step law itself
differs from the target. -/

/-- **§3's hypothesis, discharged by `Ttc.speedyMixSteps`.**

`t := Ttc.speedyMixSteps 3 (2/1) 1` satisfies the closed-form bound (by
`Ttc.speedyMixSteps_le_closedForm`), so the `n = 3` comparison holds at a step count that
is *the* speedy mixing time, not an arbitrary small numeral.

At `ρ = 1` the accompanying total-variation guarantee would be `ENNReal.ofReal 1`, i.e.
vacuous; `ρ = 1` is used here only because it is the geometry
`Ttc.SamplerCost.drawOpCharge_le_mixStepsBound_at_dim_sixteen` fixes and this witness is
about *that* comparison.  The witness with a non-vacuous tolerance is the `n = 29` one
below. -/
theorem drawOpCharge_speedyMixSteps_le_mixStepsBound_dim3 :
    (SamplerCost.drawOpCharge (speedyMixSteps 3 ((2 : ℝ) / 1) 1) 3 1 : ℝ)
      ≤ mixStepsBound 3 1 2 1 2 (1 / 2) :=
  drawOpCharge_le_mixStepsBound_at_dim_three
    (speedyMixSteps_le_closedForm 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- **THE WITNESS — no hypotheses at all, at nontrivial scaling.**

`n = 29`, `cen = 3·e₀ ≠ 0`, `γ = 1/2 ≠ 1`, `K = Metric.ball cen 1`, `Dm = 2` (so
`Dm = 4γ`), `ρ = 1/2`, `rfac = 1`; against the ball walk at `γ = 1/2`, `Dm = 2`, `δ = 1`,
`Mw = 1`, `eps = 1/2`.  At `t := Ttc.speedyMixSteps 29 (2/(1/2)) (1/2)`, three facts
simultaneously and unconditionally:

1. the lazy speedy walk with step `(1/2)·(1/2)/(4·29) = 1/464`, started from
   `Arlib.uniformOn volume (Metric.ball (3e₀) (1/2))`, is within total variation `1/2` of
   `Arlib.uniformOn volume (Metric.ball (3e₀) 1)` after `t` steps;
2. the charged price of one draw at that same `t` is at most `Ttc.mixSteps 29 (1/2) 2 1 1 (1/2)`,
   the ball walk's own step count at the same geometry and the same tolerance;
3. that price is a **positive** natural — `drawOpCharge t 29 1 = 29·(t+2) > 0` — so the
   comparison is not won by pricing nothing.

Every hypothesis of `Ttc.speedyWalk_mixes_and_drawPrice_le_poly` and of
`Ttc.drawOpCharge_le_mixSteps_at_dim_29` is discharged: `measurableSet_ball`, `convex_ball`,
`Metric.ball_subset_ball`, `Arlib.MarkovChains.dist_le_two_of_mem_ball_one`, `norm_num`, and
`Ttc.speedyMixSteps_le_closedForm` for the step count.  Nothing is left open — not even
`2 ≤ n`, since `n` is the numeral `29`.

The chart `y ↦ 3e₀ + (1/2)·y` is non-identity in **both** its translation and its scaling,
so the affine machinery of `Ttc.tvLe_transport_inscribedAffine` is genuinely exercised, and
the well-roundedness ratio `Dm/γ = 4` is the one §4's arithmetic is stated at. -/
theorem speedy_mixes_and_beats_ballWalk_dim29 :
    Arlib.TVLe
        (Arlib.MarkovChains.iterate
          (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyWalk
            (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin 29) (3 : ℝ)) 1)
            ((1 / 2 : ℝ) * ((1 / 2 : ℝ) / (4 * ((29 : ℕ) : ℝ))))))
          (Arlib.uniformOn volume
            (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin 29) (3 : ℝ)) (1 / 2 : ℝ)))
          (speedyMixSteps 29 ((2 : ℝ) / (1 / 2 : ℝ)) (1 / 2)))
        (Arlib.uniformOn volume
          (Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin 29) (3 : ℝ)) 1))
        (ENNReal.ofReal (1 / 2))
      ∧ (SamplerCost.drawOpCharge
            (speedyMixSteps 29 ((2 : ℝ) / (1 / 2 : ℝ)) (1 / 2)) 29 1 : ℝ)
          ≤ mixSteps 29 (1 / 2) 2 1 1 (1 / 2)
      ∧ 0 < SamplerCost.drawOpCharge (speedyMixSteps 29 ((2 : ℝ) / (1 / 2 : ℝ)) (1 / 2)) 29 1 := by
  have hmain := speedyWalk_mixes_and_drawPrice_le_poly (n := 29) (by norm_num)
    (K := Metric.ball (EuclideanSpace.single (⟨0, by omega⟩ : Fin 29) (3 : ℝ)) 1)
    measurableSet_ball (convex_ball _ _) (γ := 1 / 2) (by norm_num)
    (Metric.ball_subset_ball (by norm_num)) (Dm := 2)
    (Arlib.MarkovChains.dist_le_two_of_mem_ball_one _) (by norm_num) (rho := 1 / 2)
    (by norm_num) (by norm_num) (rfac := 1) le_rfl
  refine ⟨hmain.1, ?_, ?_⟩
  · exact drawOpCharge_le_mixSteps_at_dim_29 (γ := 1 / 2) (Dm := 2) (δ := 1) (by norm_num)
      (by norm_num) (by norm_num)
      (speedyMixSteps_le_closedForm 29 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
  · have hc : SamplerCost.stepOpCharge 29 1 = 29 := by
      unfold SamplerCost.stepOpCharge
      norm_num
    unfold SamplerCost.drawOpCharge
    rw [hc]
    omega

/-! ### Axiom audit (`CLAUDE.md` §4)

Target for every line: `[propext, Classical.choice, Quot.sound]`.

What `#print axioms` **cannot** see, and what the module docstring says instead: that these
are charges in a cost model rather than running times; that `Ttc.SamplerCost.stepOpCharge`
measures no executable; and that the chain to `Ttc.ttcSampPrice` at TTC's own arguments is
**not** closed. -/

#print axioms speedyMixSteps_le_closedForm
#print axioms speedyWalk_mixes_and_drawPrice_le_poly
#print axioms expTerm_lt_polyPrice_at_dim_two
#print axioms polyPrice_le_expTerm_at_dim_three
#print axioms drawOpCharge_le_mixStepsBound_at_dim_three
#print axioms polyPrice_le_expLowerBound_at_dim_29
#print axioms drawOpCharge_le_mixSteps_at_dim_29
#print axioms drawOpCharge_speedyMixSteps_le_mixStepsBound_dim3
#print axioms speedy_mixes_and_beats_ballWalk_dim29

end Ttc
