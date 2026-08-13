/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.SamplerCost
import Ttc.Exec.SamplePrice

/-!
# A **polynomial** per-sample price, priced on a hypothesised polynomial step count

`Ttc.ttcSampPrice` (`Ttc/Exec/SamplePrice.lean:111`) is `⌈Ttc.ttcSampStepsPrice …⌉₊`, and
`Ttc.ttcSampStepsPrice` is `Ttc.mixStepsBound` at cube-free arguments
(`Ttc/Exec/InflateBound.lean:667`, `rfl`).  `Ttc.mixStepsBound`
(`Ttc/Exec/SampleBound.lean:219`) is

```
(log Mw + 2 log(1/eps)) · (1024·((γ+Dm)/γ)^{2n} + 16384·4ⁿ·n²·Dm²/dl²·((γ+Dm)/γ)^{4n}) + 1
```

— **exponential in `n`**, and `Arlib/MarkovChains/Continuous/EllFloor.lean` shows the route
that produces it (a *pointwise* local-conductance floor) is necessarily exponential.

This file prices the polynomial alternative.  It takes the polynomial step count as a
**hypothesis** and proves the arithmetic on top of it, so that "exponential → polynomial"
becomes a machine-checked comparison rather than a claim in prose.

## What is a hypothesis here, and what is proved

**Hypothesis.**  Every price theorem below binds a natural `t` together with

```
ht : (t : ℝ) ≤ (2n·log(1+D) + 2·log(2/ρ)) / (min (1/32) (1/(8D) · (ρ/(4n)) / (256n)))² + 1
```

with `D` the diameter of the *rescaled* body.  That right-hand side is **verbatim** the
step count of `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps`
(`Arlib/MarkovChains/Continuous/UniformSamplerUncond.lean:344-346`), which is
`Arlib.MarkovChains.conductanceMixingTime_le` applied at that theorem's conductance
`φ = min(1/32, κδ/(256n))` with `κ = 1/(8D)`, `δ = ρ/(4n)`, and warmness `M = (1+D)^{2n}`.
Taking it verbatim is deliberate: a backend that runs the walk for
`conductanceMixingTime ((1+D)^(2n)) (min …) (ρ/2)` steps discharges `ht` and the mixing
theorem's own `ht` at once, so the composition is a one-line step.

**Nothing in this file proves that any walk mixes.**  The mixing theorem lives in
`Arlib/MarkovChains/Continuous/UniformSamplerUncond.lean`; the geometry that transports it
onto TTC's bodies, and the TTC-side backend that runs it, are separate files.  This file is
*only* the pricing arithmetic — it is deliberately stated so that it can be composed with
them without either being read here.

**Proved.**  The closed form above is `O(n⁵·D²·(log(1+D)+log(2/ρ))/ρ²)`
(`Ttc.SamplerCost.speedySteps_le_poly`), hence the charged price of one draw is

```
drawOpCharge t n rfac ≤ 2³⁰ · n⁶ · rfac · (Dm/γ)² · (log(1+Dm/γ) + log(2/ρ)) / ρ²
```

(`Ttc.SamplerCost.drawOpCharge_le_poly`) — **polynomial in `n`**, with every suppressed
factor printed.

## The well-roundedness cost, stated explicitly

The speedy-walk theorem needs `ball 0 1 ⊆ K`.  TTC's bodies carry an inradius `γ` and a
diameter `Dm` instead, so the body must be rescaled by `1/γ` before the theorem applies;
the rescaled diameter is `Dm/γ`.  **That is why `(Dm/γ)²` — not `Dm²` — appears in the
price**, and why `2γ ≤ Dm` (a body of inradius `γ` has diameter at least `2γ`) is a binder
rather than a remark.  The factor is *visible in every statement*, never inside a constant.
`(R/γ)²`-type factors are accepted here; they are not hidden.

The rescaling pushforward itself (that `x ↦ x/γ` carries the body, its uniform measure and
the walk) is **not proved here** — it is the geometry file's job.  What is proved here is
that once the count is stated at the rescaled diameter, the price is polynomial in `n`.

## The comparison against the exponential price

* `Ttc.SamplerCost.expTerm_le_mixStepsBound` — the exponential summand
  `(log Mw + 2 log(1/eps))·16384·4ⁿ·n²·Dm²/dl²·((γ+Dm)/γ)^{4n}` is a lower bound for
  `Ttc.mixStepsBound`.
* `Ttc.SamplerCost.mixStepsBound_le_ttcSampPrice` — and `Ttc.mixStepsBound` at TTC's own
  arguments is a lower bound for `Ttc.ttcSampPrice`, by `Nat.le_ceil`.  So the chain
  terminates at the actual price object.
* `Ttc.SamplerCost.drawOpCharge_le_mixStepsBound_at_dim_sixteen` — at `n = 16`, `γ = 1`,
  `Dm = 2`, `dl = 1`, `Mw = 2`, `eps = 1/2`, `ρ = rfac = 1`: **the whole polynomial draw
  price is at most the exponential step count**, machine-checked.
* `Ttc.SamplerCost.polyPrice_isLittleO_mixStepsBound` — and asymptotically the polynomial
  price is `o(Ttc.mixStepsBound)` at *any* fixed geometry with `γ ≤ Dm`.

**Why `n = 16` and not the smallest admissible dimension.**  The constant `2³⁰` here is
large, and at `n = 2` with this same geometry the comparison is *false* (by hand:
`2³⁰·2⁶·4·(log 3 + log 2) ≈ 4.9·10¹¹` against `3·log 2·2¹⁴·4²·2²·4·3⁸ ≈ 5.7·10¹⁰`; those
two numbers are **not** machine-checked, only the `n = 16` statement is).  This is stated
rather than hidden: "polynomial beats exponential" is an asymptotic claim, `n = 16` is
chosen with a margin of `3⁶⁴ ≈ 3.4·10³⁰`, and
`Ttc.SamplerCost.polyPrice_isLittleO_mixStepsBound` is the statement that carries the
asymptotics.  Nothing more is claimed.

## Scope — what a smaller charged price is NOT

**This file does not make TTC polynomial-time, and nothing here is a running time.**

* `Ttc.stepCost` counts oracle calls; the arithmetic inside a step is priced at **zero**
  (`Ttc/CostModel.lean:87-91`).
* `Ttc.VolumeAlgorithm` (`Ttc/Volume/Oracle.lean:70`) has **no complexity field** — its
  fields are `Ω`, `mΩ`, `μ`, `isProb`, `est` and its measurability/accuracy guards, so
  there is no runtime in the model to bound in the first place.
* The sampler's rounding/rejection stage is **not costed at all**: `Ttc.kv97SampD` is a
  density, consumes no coin sequence, and no coin-consuming object performing the rejection
  loop exists in this development (`Ttc/CostModel.lean:84`).
* The `while` loops of `alg:ttc` lines 32–42 are **uncharged** (`Ttc/CostModel.lean:85`).
* `Ttc.mixSteps` prices the chain the sampler's *law* is defined by, not steps the modelled
  run takes (`Ttc/Exec/SamplePrice.lean:77-80`).

A bound on an undercount is not a bound on the count.  What is genuinely established is:
*the count that `Ttc.mixStepsBound` charges is exponential in `n`, and the count a speedy
walk would charge — assumed here, proved elsewhere — is polynomial, and the pricing
arithmetic that turns the second into a per-draw charge preserves polynomiality.*

## No new definitions

Every declaration below is a `theorem`.  The price is `Ttc.SamplerCost.drawOpCharge`, which
already exists and which `Ttc.SamplerCost.samplePrice` is definitionally built from
(`samplePrice n γ R M ε' rfac = drawOpCharge (stepsPrice n γ R M ε') n rfac`); leaving the
step count a free argument is exactly what lets a *different* step count be priced without
a second cost model.  The `Ttc.SamplerCost.stepOpCharge` modelling caveat
(`Ttc/Exec/SamplerCost.lean:360-362`) is inherited unchanged: no executable step is measured
by it.
-/

namespace Ttc.SamplerCost

open Real

set_option maxRecDepth 100000

/-! ## 1. The conductance `min` collapses to its second branch

At `κ = 1/(8D)` and `δ = ρ/(4n)` the speedy-walk conductance is
`min(1/32, ρ/(8192·D·n²))`, and the second branch is always the smaller one in the regime
of interest (`D ≥ 1/2`, `ρ ≤ 1`, `n ≥ 1`). -/

/-- **`min(1/32, (1/(8D))·(ρ/(4n))/(256n)) = ρ/(8192·D·n²)`.**

The identity that makes the step count of
`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps` a rational function
of `n`, `D` and `ρ` rather than a `min`.  The hypotheses are exactly what makes the second
branch smaller: `32ρ ≤ 8192·D·n²` follows from `ρ ≤ 1`, `D ≥ 1/2`, `n ≥ 1`. -/
theorem speedyPhi_eq (n : ℕ) {D rho : ℝ} (hn : 1 ≤ n) (hD : 1 / 2 ≤ D)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    min (1 / 32 : ℝ) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))
      = rho / (8192 * D * (n : ℝ) ^ 2) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hD0 : (0 : ℝ) < D := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have heq : 1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ))
      = rho / (8192 * D * (n : ℝ) ^ 2) := by
    field_simp
    ring
  rw [heq, min_eq_right]
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have hDn : (1 : ℝ) / 2 ≤ D * (n : ℝ) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-! ## 2. The step count is polynomial — the pure arithmetic

Stated with the two logarithms abstracted to `L1`, `L2` so that the inequality is visible
as real arithmetic with no analysis in it. -/

/-- **The arithmetic heart.**  With `φ = ρ/(8192·D·n²)`,

```
(2n·L1 + 2·L2)/φ² + 1  ≤  2²⁸ · n⁵ · D² · (L1 + L2) / ρ² .
```

The two constants: `8192² = 2²⁶`, and `2n·(L1+L2)·2²⁶ = 2²⁷·n·(L1+L2)`, so the honest
constant is `2²⁷`; the doubling to `2²⁸` is what absorbs the trailing `+ 1`, which is the
`Nat.ceil` slack of `Arlib.MarkovChains.mixingTime`.  `L2 ≥ 0.69` is `log(2/ρ) ≥ log 2` and
is what makes that absorption legal. -/
theorem steps_arith_le {nR D rho L1 L2 : ℝ} (hn2 : 2 ≤ nR) (hD : 1 / 2 ≤ D)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) (hL1 : 0 ≤ L1) (hL2 : 0.69 ≤ L2) :
    (2 * nR * L1 + 2 * L2) / (rho / (8192 * D * nR ^ 2)) ^ 2 + 1
      ≤ 2 ^ 28 * nR ^ 5 * D ^ 2 * (L1 + L2) / rho ^ 2 := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hn0 : (0 : ℝ) < nR := by linarith
  have hrho2 : (0 : ℝ) < rho ^ 2 := by positivity
  have hrho2le : rho ^ 2 ≤ 1 := by nlinarith
  -- rewrite the division by `φ²` as a multiplication by `(8192 D n²)²`
  have hrw : (2 * nR * L1 + 2 * L2) / (rho / (8192 * D * nR ^ 2)) ^ 2
      = (2 * nR * L1 + 2 * L2) * (8192 * D * nR ^ 2) ^ 2 / rho ^ 2 := by
    rw [div_pow, div_div_eq_mul_div]
  rw [hrw]
  -- lower bounds on the polynomial factor
  have hn5 : (32 : ℝ) ≤ nR ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 5
    norm_num at h
    linarith
  have hD2 : (1 : ℝ) / 4 ≤ D ^ 2 := by nlinarith
  have hS0 : (0.69 : ℝ) ≤ L1 + L2 := by linarith
  have hW1 : (32 : ℝ) * (1 / 4) ≤ nR ^ 5 * D ^ 2 := by nlinarith
  have hW : (1 : ℝ) ≤ nR ^ 5 * D ^ 2 * (L1 + L2) := by nlinarith
  -- the numerator estimate `2n·L1 + 2·L2 ≤ 2n·(L1 + L2)`
  have hnum : 2 * nR * L1 + 2 * L2 ≤ 2 * nR * (L1 + L2) := by nlinarith
  have hQ0 : (0 : ℝ) ≤ (8192 * D * nR ^ 2) ^ 2 := sq_nonneg _
  have hstep : (2 * nR * L1 + 2 * L2) * (8192 * D * nR ^ 2) ^ 2
      ≤ 134217728 * (nR ^ 5 * D ^ 2 * (L1 + L2)) := by
    calc (2 * nR * L1 + 2 * L2) * (8192 * D * nR ^ 2) ^ 2
        ≤ (2 * nR * (L1 + L2)) * (8192 * D * nR ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hnum hQ0
      _ = 134217728 * (nR ^ 5 * D ^ 2 * (L1 + L2)) := by ring
  have hfinal : (2 * nR * L1 + 2 * L2) * (8192 * D * nR ^ 2) ^ 2 + rho ^ 2
      ≤ 2 ^ 28 * nR ^ 5 * D ^ 2 * (L1 + L2) := by
    have h1 : 2 ^ 28 * nR ^ 5 * D ^ 2 * (L1 + L2)
        = 268435456 * (nR ^ 5 * D ^ 2 * (L1 + L2)) := by ring
    rw [h1]
    linarith
  calc (2 * nR * L1 + 2 * L2) * (8192 * D * nR ^ 2) ^ 2 / rho ^ 2 + 1
      = ((2 * nR * L1 + 2 * L2) * (8192 * D * nR ^ 2) ^ 2 + rho ^ 2) / rho ^ 2 := by
        field_simp
    _ ≤ (2 ^ 28 * nR ^ 5 * D ^ 2 * (L1 + L2)) / rho ^ 2 := by gcongr
    _ = 2 ^ 28 * nR ^ 5 * D ^ 2 * (L1 + L2) / rho ^ 2 := rfl

/-! ## 3. The step count of the speedy walk, bounded by a polynomial -/

/-- **The closed-form speedy-walk step count is `O(n⁵·D²·(log(1+D)+log(2/ρ))/ρ²)`.**

The left-hand side is *verbatim* the hypothesis of
`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn_uncond_steps`
(`Arlib/MarkovChains/Continuous/UniformSamplerUncond.lean:344-346`), i.e. the count that
`Arlib.MarkovChains.conductanceMixingTime_le` produces from `M = (1+D)^{2n}` and
`φ = min(1/32, (1/(8D))·(ρ/(4n))/(256n))`.

`D` here is the diameter of a body containing the unit ball, hence `D ≥ 1/2`; `2 ≤ n`
mirrors the real scope limit of the mixing theorem (it is the hypothesis of
`Arlib.hiso_ellProb_of_ball_bound`) and is not widened. -/
theorem speedySteps_le_poly (n : ℕ) {D rho : ℝ} (hn : 2 ≤ n) (hD : 1 / 2 ≤ D)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    (2 * (n : ℝ) * Real.log (1 + D) + 2 * Real.log (2 / rho))
        / (min (1 / 32 : ℝ) (1 / (8 * D) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2 + 1
      ≤ 2 ^ 28 * (n : ℝ) ^ 5 * D ^ 2
          * (Real.log (1 + D) + Real.log (2 / rho)) / rho ^ 2 := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog1 : (0 : ℝ) ≤ Real.log (1 + D) := Real.log_nonneg (by linarith)
  have hlog2 : (0.69 : ℝ) ≤ Real.log (2 / rho) := by
    have h := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log (2 / rho) := by
      refine Real.log_le_log (by norm_num) ?_
      rw [le_div_iff₀ hrho0]
      linarith
    linarith
  rw [speedyPhi_eq n hn1 hD hrho0 hrho1]
  exact steps_arith_le hnR hD hrho0 hrho1 hlog1 hlog2

/-- **The same at TTC's geometry, with the well-roundedness factor `(Dm/γ)²` explicit.**

A TTC body has inradius `γ` and diameter `Dm`; rescaling by `1/γ` puts the unit ball inside
it and turns the diameter into `Dm/γ`.  `2*γ ≤ Dm` is the (unavoidable) fact that a body
containing a ball of radius `γ` has diameter at least `2γ`.

The `(Dm/γ)²` is the **price of well-roundedness**, and it is printed, not absorbed. -/
theorem speedySteps_rescaled_le_poly (n : ℕ) {γ Dm rho : ℝ} (hn : 2 ≤ n) (hγ0 : 0 < γ)
    (hγD : 2 * γ ≤ Dm) (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    (2 * (n : ℝ) * Real.log (1 + Dm / γ) + 2 * Real.log (2 / rho))
        / (min (1 / 32 : ℝ)
            (1 / (8 * (Dm / γ)) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2 + 1
      ≤ 2 ^ 28 * (n : ℝ) ^ 5 * (Dm / γ) ^ 2
          * (Real.log (1 + Dm / γ) + Real.log (2 / rho)) / rho ^ 2 := by
  have hDg : (2 : ℝ) ≤ Dm / γ := by
    rw [le_div_iff₀ hγ0]
    linarith
  exact speedySteps_le_poly n hn (by linarith) hrho0 hrho1

/-! ## 4. THE PRICE — polynomial in `n` -/

/-- **THE POLYNOMIAL PER-DRAW PRICE.**

```
drawOpCharge t n rfac ≤ 2³⁰ · n⁶ · rfac · (Dm/γ)² · (log(1+Dm/γ) + log(2/ρ)) / ρ²
```

for **any** `t` bounded by the speedy walk's closed-form step count at the rescaled
diameter `Dm/γ`.  This is the same shape as `Ttc.SamplerCost.samplePrice_le_quartic_eps`
(`Ttc/Exec/SampPriceEps.lean:183`) —

```
samplePrice n γ R M ε' rfac ≤ 2⁶² · n³ · rfac · (R²/γ²) · (n·log(2R) + log(1/ε'))
```

— constant · `n^k` · `rfac` · squared geometric ratio · logarithms, and it is drop-in for
`Ttc.SamplerCost.samplePrice` because `samplePrice n γ R M ε' rfac` *is*
`drawOpCharge (stepsPrice n γ R M ε') n rfac` by definition.  Leaving `t` free is the whole
point: the price arithmetic no longer depends on which chain supplies the count.

Every hypothesis is named and nothing is suppressed:

* `hn : 2 ≤ n` — the mixing theorem's own scope limit;
* `hrfac : 1 ≤ rfac` — the facet count, charged at `⌈n·rfac⌉₊` per step, not suppressed;
* `hγ0 : 0 < γ`, `hγD : 2γ ≤ Dm` — the geometry; `(Dm/γ)²` is **printed**;
* `hrho0 : 0 < ρ`, `hrho1 : ρ ≤ 1` — the sampler's TV accuracy; `log(2/ρ)` and `1/ρ²` are
  **printed**;
* `ht` — the polynomial step count, a **hypothesis** (module docstring).

⚠ Not a running time: see the module docstring's scope section. -/
theorem drawOpCharge_le_poly (n : ℕ) {γ Dm rho rfac : ℝ} {t : ℕ} (hn : 2 ≤ n)
    (hrfac : 1 ≤ rfac) (hγ0 : 0 < γ) (hγD : 2 * γ ≤ Dm) (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (ht : (t : ℝ)
      ≤ (2 * (n : ℝ) * Real.log (1 + Dm / γ) + 2 * Real.log (2 / rho))
          / (min (1 / 32 : ℝ)
              (1 / (8 * (Dm / γ)) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2 + 1) :
    (drawOpCharge t n rfac : ℝ)
      ≤ 2 ^ 30 * (n : ℝ) ^ 6 * rfac * (Dm / γ) ^ 2
          * (Real.log (1 + Dm / γ) + Real.log (2 / rho)) / rho ^ 2 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hDg : (2 : ℝ) ≤ Dm / γ := by
    rw [le_div_iff₀ hγ0]
    linarith
  have hrho2 : (0 : ℝ) < rho ^ 2 := by positivity
  have hrho2le : rho ^ 2 ≤ 1 := by nlinarith
  have hlog1 : (0 : ℝ) ≤ Real.log (1 + Dm / γ) := Real.log_nonneg (by linarith)
  have hlog2 : (0.69 : ℝ) ≤ Real.log (2 / rho) := by
    have h := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log (2 / rho) := by
      refine Real.log_le_log (by norm_num) ?_
      rw [le_div_iff₀ hrho0]
      linarith
    linarith
  have htP : (t : ℝ) ≤ 2 ^ 28 * (n : ℝ) ^ 5 * (Dm / γ) ^ 2
      * (Real.log (1 + Dm / γ) + Real.log (2 / rho)) / rho ^ 2 :=
    ht.trans (speedySteps_rescaled_le_poly n hn hγ0 hγD hrho0 hrho1)
  -- the polynomial count is at least `2`, which absorbs the `+ 2` of `drawOpCharge`
  have hn5 : (32 : ℝ) ≤ (n : ℝ) ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnR 5
    norm_num at h
    linarith
  have hd2 : (4 : ℝ) ≤ (Dm / γ) ^ 2 := by nlinarith
  have hS : (0.69 : ℝ) ≤ Real.log (1 + Dm / γ) + Real.log (2 / rho) := by linarith
  have hA1 : (128 : ℝ) ≤ (n : ℝ) ^ 5 * (Dm / γ) ^ 2 := by nlinarith
  have hA2 : (88 : ℝ) ≤ (n : ℝ) ^ 5 * (Dm / γ) ^ 2
      * (Real.log (1 + Dm / γ) + Real.log (2 / rho)) := by nlinarith
  have hP2 : (2 : ℝ) ≤ 2 ^ 28 * (n : ℝ) ^ 5 * (Dm / γ) ^ 2
      * (Real.log (1 + Dm / γ) + Real.log (2 / rho)) / rho ^ 2 := by
    rw [le_div_iff₀ hrho2]
    have h1 : 2 ^ 28 * (n : ℝ) ^ 5 * (Dm / γ) ^ 2
        * (Real.log (1 + Dm / γ) + Real.log (2 / rho))
        = 268435456 * ((n : ℝ) ^ 5 * (Dm / γ) ^ 2
            * (Real.log (1 + Dm / γ) + Real.log (2 / rho))) := by ring
    rw [h1]
    linarith
  -- the per-step arithmetic charge
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hC : ((stepOpCharge n rfac : ℕ) : ℝ) ≤ 2 * (n : ℝ) * rfac := by
    unfold stepOpCharge
    have h1 : ((⌈(n : ℝ) * rfac⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) * rfac + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    nlinarith
  have hC0 : (0 : ℝ) ≤ ((stepOpCharge n rfac : ℕ) : ℝ) := Nat.cast_nonneg _
  set P : ℝ := 2 ^ 28 * (n : ℝ) ^ 5 * (Dm / γ) ^ 2
      * (Real.log (1 + Dm / γ) + Real.log (2 / rho)) / rho ^ 2 with hPdef
  have hb0 : (0 : ℝ) ≤ 2 * P := by linarith
  have hsum : (t : ℝ) + 2 ≤ 2 * P := by linarith
  have hfinal : (drawOpCharge t n rfac : ℝ) ≤ 2 * P * (2 * (n : ℝ) * rfac) := by
    unfold drawOpCharge
    push_cast
    exact mul_le_mul hsum hC hC0 hb0
  refine hfinal.trans_eq ?_
  rw [hPdef]
  ring

/-- **"Drop-in" made machine-checked**: `Ttc.SamplerCost.samplePrice` *is*
`Ttc.SamplerCost.drawOpCharge` at the hit-and-run step count.

So `Ttc.SamplerCost.drawOpCharge_le_poly` prices `samplePrice` verbatim the moment a
backend substitutes its own `t` for `Ttc.SamplerCost.stepsPrice` — no second cost model, no
new `def`, and the constant/exponent bookkeeping of
`Ttc.SamplerCost.samplePrice_le_quartic_eps` is untouched. -/
theorem samplePrice_eq_drawOpCharge (n : ℕ) (γ R M epsPrime rfac : ℝ) :
    samplePrice n γ R M epsPrime rfac
      = drawOpCharge (stepsPrice n γ R M epsPrime) n rfac := rfl

/-! ## 5. The exponential price it replaces -/

/-- **`Ttc.mixStepsBound` is at least its exponential summand.**

`mixStepsBound = L·(1024·B^{2n} + 16384·4ⁿ·n²·Dm²/dl²·B^{4n}) + 1` with
`L = log Mw + 2 log(1/eps) ≥ 0` and `B = (γ+Dm)/γ`; dropping the first summand and the
`+ 1` is the whole proof.  What is left is `Θ(4ⁿ·(γ+Dm)^{4n}/γ^{4n})` — the exponential
that `Ttc.ttcSampPrice` inherits.

No `0 < dl` binder is needed: at `dl = 0` Lean's `x / 0 = 0` convention makes the left-hand
side `0`, and the inequality is trivial.  `hγ0`/`hDm0` are likewise only there to name the
regime the geometry actually lives in. -/
theorem expTerm_le_mixStepsBound (n : ℕ) {γ Dm dl Mw eps : ℝ} (hγ0 : 0 < γ) (hDm0 : 0 < Dm)
    (hMw : 1 ≤ Mw) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    (Real.log Mw + 2 * Real.log (1 / eps))
        * (16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2 * ((γ + Dm) / γ) ^ (4 * n))
      ≤ mixStepsBound n γ Dm dl Mw eps := by
  have hlogM : (0 : ℝ) ≤ Real.log Mw := Real.log_nonneg hMw
  have hlogE : (0 : ℝ) ≤ Real.log (1 / eps) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ heps0]
    linarith
  have hL0 : (0 : ℝ) ≤ Real.log Mw + 2 * Real.log (1 / eps) := by linarith
  have hB0 : (0 : ℝ) ≤ 1024 * ((γ + Dm) / γ) ^ (2 * n) := by positivity
  have hprod : (0 : ℝ) ≤ (Real.log Mw + 2 * Real.log (1 / eps))
      * (1024 * ((γ + Dm) / γ) ^ (2 * n)) := mul_nonneg hL0 hB0
  unfold mixStepsBound
  nlinarith [hprod]

/-- **The exponential closed form really is a lower bound for the TTC price.**

`Ttc.ttcSampPrice = ⌈Ttc.ttcSampStepsPrice⌉₊` (`Ttc/Exec/SamplePrice.lean:111`), and
`Ttc.ttcSampStepsPrice = Ttc.mixStepsBound` at TTC's own cube-free arguments
(`Ttc/Exec/InflateBound.lean:667`, by `rfl`).  So the comparison chain of this file
terminates at the *actual* price object rather than at a surrogate. -/
theorem mixStepsBound_le_ttcSampPrice {A : Type*} {n : ℕ} (atoms : A → LinAtom n)
    (φ : BForm A) (ε δ : ℝ) :
    mixStepsBound n (ttcSampInradius atoms φ ε δ) (ttcSampDiamPrice atoms φ ε δ)
        (ttcSampStep atoms φ ε δ) (ttcSampWarmPrice atoms φ ε δ)
        (ttcSampTolPrice atoms φ ε δ)
      ≤ (ttcSampPrice atoms φ ε δ : ℝ) :=
  Nat.le_ceil _

/-! ## 6. The comparison, machine-checked -/

/-- **Polynomial beats exponential at `n = 16`, at unit-ish geometry.**

`γ = 1`, `Dm = 2` (so the rescaled diameter is `2` and `(γ+Dm)/γ = 3`), `dl = 1`, `Mw = 2`,
`eps = 1/2`, `ρ = 1`, `rfac = 1`.  Both sides collapse to `2⁵⁶` times a logarithm:

* polynomial price bound `= 2³⁰ · 16⁶ · 4 · (log 3 + log 2) = 2⁵⁶ · (log 3 + log 2)`;
* exponential summand `= 3·log 2 · 2¹⁴ · 4¹⁶ · 16² · 4 · 3⁶⁴ = 3·log 2 · 2⁵⁶ · 3⁶⁴`.

and `log 3 + log 2 ≤ 3·log 2 ≤ 3·log 2 · 3⁶⁴` because `3 ≤ 4 = 2²`.  The margin is the
factor `3⁶⁴ ≈ 3.4·10³⁰`. -/
theorem polyPrice_le_expTerm_at_dim_sixteen :
    2 ^ 30 * ((16 : ℕ) : ℝ) ^ 6 * 1 * ((2 : ℝ) / 1) ^ 2
        * (Real.log (1 + (2 : ℝ) / 1) + Real.log (2 / (1 : ℝ))) / (1 : ℝ) ^ 2
      ≤ (Real.log 2 + 2 * Real.log (1 / (1 / 2 : ℝ)))
          * (16384 * 4 ^ (16 : ℕ) * ((16 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ 2 / (1 : ℝ) ^ 2
              * (((1 : ℝ) + 2) / 1) ^ (4 * (16 : ℕ))) := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := by
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
  have hbig : (1 : ℝ) ≤ (((1 : ℝ) + 2) / 1) ^ (4 * (16 : ℕ)) := by
    refine one_le_pow₀ ?_
    norm_num
  rw [hinv]
  have hlhs : 2 ^ 30 * ((16 : ℕ) : ℝ) ^ 6 * 1 * ((2 : ℝ) / 1) ^ 2
      * (Real.log (1 + (2 : ℝ) / 1) + Real.log (2 / (1 : ℝ))) / (1 : ℝ) ^ 2
      = 72057594037927936 * (Real.log 3 + Real.log 2) := by
    norm_num
  have hrhs : (Real.log 2 + 2 * Real.log 2)
      * (16384 * 4 ^ (16 : ℕ) * ((16 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ 2 / (1 : ℝ) ^ 2
          * (((1 : ℝ) + 2) / 1) ^ (4 * (16 : ℕ)))
      = 72057594037927936 * (3 * Real.log 2) * (((1 : ℝ) + 2) / 1) ^ (4 * (16 : ℕ)) := by
    norm_num
    ring
  rw [hlhs, hrhs]
  have hstep : Real.log 3 + Real.log 2 ≤ 3 * Real.log 2 := by linarith
  have hstep2 : (3 : ℝ) * Real.log 2
      ≤ 3 * Real.log 2 * (((1 : ℝ) + 2) / 1) ^ (4 * (16 : ℕ)) := by
    nlinarith
  nlinarith

/-- **The whole polynomial draw price is below the exponential step count, at `n = 16`.**

`drawOpCharge_le_poly` at `n = 16, γ = 1, Dm = 2, ρ = rfac = 1`, composed with
`expTerm_le_mixStepsBound` at `n = 16, γ = 1, Dm = 2, dl = 1, Mw = 2, eps = 1/2` through
`polyPrice_le_expTerm_at_dim_sixteen`.  The conclusion mentions no bound and no constant —
it compares the two *prices* directly:

```
drawOpCharge t 16 1 ≤ mixStepsBound 16 1 2 1 2 (1/2)
```

for every `t` the speedy walk's closed-form count admits. -/
theorem drawOpCharge_le_mixStepsBound_at_dim_sixteen {t : ℕ}
    (ht : (t : ℝ)
      ≤ (2 * ((16 : ℕ) : ℝ) * Real.log (1 + (2 : ℝ) / 1) + 2 * Real.log (2 / (1 : ℝ)))
          / (min (1 / 32 : ℝ)
              (1 / (8 * ((2 : ℝ) / 1)) * ((1 : ℝ) / (4 * ((16 : ℕ) : ℝ)))
                / (256 * ((16 : ℕ) : ℝ)))) ^ 2 + 1) :
    (drawOpCharge t 16 1 : ℝ) ≤ mixStepsBound 16 1 2 1 2 (1 / 2) := by
  have h1 := drawOpCharge_le_poly (n := 16) (γ := 1) (Dm := 2) (rho := 1) (rfac := 1)
    (t := t) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl ht
  have h2 := expTerm_le_mixStepsBound (n := 16) (γ := 1) (Dm := 2) (dl := 1) (Mw := 2)
    (eps := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := polyPrice_le_expTerm_at_dim_sixteen
  linarith

/-- **Asymptotically, the polynomial price is `o(Ttc.mixStepsBound)`** — at any fixed
geometry with `γ ≤ Dm`, any fixed step size, warmness and accuracy.

The witness is `n⁶ = o(64ⁿ)`: with `γ ≤ Dm` the exponential base `4·((γ+Dm)/γ)⁴` is at
least `4·2⁴ = 64`.  `2 ≤ Mw` is what keeps `log Mw + 2 log(1/eps)` bounded away from `0`
(at `Mw = 1, eps = 1` the exponential price degenerates to the constant `1`). -/
theorem polyPrice_isLittleO_mixStepsBound {γ Dm dl Mw eps rho rfac : ℝ}
    (hγ0 : 0 < γ) (hγD : γ ≤ Dm) (hdl0 : 0 < dl) (hMw : 2 ≤ Mw)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ => 2 ^ 30 * (n : ℝ) ^ 6 * rfac * (Dm / γ) ^ 2
        * (Real.log (1 + Dm / γ) + Real.log (2 / rho)) / rho ^ 2)
      (fun n : ℕ => mixStepsBound n γ Dm dl Mw eps) := by
  have hDm0 : (0 : ℝ) < Dm := lt_of_lt_of_le hγ0 hγD
  have hB : (2 : ℝ) ≤ (γ + Dm) / γ := by
    rw [le_div_iff₀ hγ0]
    linarith
  have hlogMw : Real.log 2 ≤ Real.log Mw := Real.log_le_log (by norm_num) hMw
  have hlog2pos : (0 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogE : (0 : ℝ) ≤ Real.log (1 / eps) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ heps0]
    linarith
  -- the constant against which `64ⁿ` is compared
  set K : ℝ := Real.log 2 * 16384 * (Dm ^ 2 / dl ^ 2) with hKdef
  have hK0 : (0 : ℝ) < K := by
    rw [hKdef]
    have : (0 : ℝ) < Dm ^ 2 / dl ^ 2 := by positivity
    positivity
  -- `Kn · 64ⁿ ≤ mixStepsBound n` for `n ≥ 1`
  have hbig : Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (64 : ℝ) ^ n)
      (fun n : ℕ => mixStepsBound n γ Dm dl Mw eps) := by
    refine Asymptotics.IsBigO.of_bound (1 / K) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    have hpow : (64 : ℝ) ^ n = 4 ^ n * (2 : ℝ) ^ (4 * n) := by
      rw [pow_mul, ← mul_pow]
      norm_num
    have hBn : (2 : ℝ) ^ (4 * n) ≤ ((γ + Dm) / γ) ^ (4 * n) :=
      pow_le_pow_left₀ (by norm_num) hB _
    have h4n : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
    have hlow : K * (64 : ℝ) ^ n
        ≤ (Real.log Mw + 2 * Real.log (1 / eps))
            * (16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2
                * ((γ + Dm) / γ) ^ (4 * n)) := by
      have hL : Real.log 2 ≤ Real.log Mw + 2 * Real.log (1 / eps) := by linarith
      have hstep1 : K * (64 : ℝ) ^ n
          ≤ Real.log 2 * (16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2
              * ((γ + Dm) / γ) ^ (4 * n)) := by
        rw [hKdef, hpow]
        have hd : (0 : ℝ) < Dm ^ 2 / dl ^ 2 := by positivity
        have e1 : Real.log 2 * 16384 * (Dm ^ 2 / dl ^ 2) * (4 ^ n * (2 : ℝ) ^ (4 * n))
            = (Real.log 2 * 16384 * (Dm ^ 2 / dl ^ 2) * 4 ^ n) * (2 : ℝ) ^ (4 * n) := by
          ring
        have e2 : Real.log 2 * (16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2
              * ((γ + Dm) / γ) ^ (4 * n))
            = (Real.log 2 * 16384 * (Dm ^ 2 / dl ^ 2) * 4 ^ n) * (n : ℝ) ^ 2
                * ((γ + Dm) / γ) ^ (4 * n) := by
          field_simp
        rw [e1, e2]
        have hc0 : (0 : ℝ) < Real.log 2 * 16384 * (Dm ^ 2 / dl ^ 2) * 4 ^ n := by positivity
        have hB0 : (0 : ℝ) ≤ ((γ + Dm) / γ) ^ (4 * n) := by positivity
        have h2n0 : (0 : ℝ) < (2 : ℝ) ^ (4 * n) := by positivity
        nlinarith [mul_nonneg (le_of_lt hc0) hB0]
      have hfac0 : (0 : ℝ) ≤ 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2
          * ((γ + Dm) / γ) ^ (4 * n) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hL hfac0]
    have hmix := expTerm_le_mixStepsBound n (γ := γ) (Dm := Dm) (dl := dl) (Mw := Mw)
      (eps := eps) hγ0 hDm0 (by linarith) heps0 heps1
    have hmix0 : (0 : ℝ) ≤ mixStepsBound n γ Dm dl Mw eps := by
      have h0 : (0 : ℝ) ≤ K * (64 : ℝ) ^ n := by positivity
      linarith
    rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (64 : ℝ) ^ n),
      Real.norm_of_nonneg hmix0]
    rw [div_mul_eq_mul_div, le_div_iff₀ hK0]
    linarith
  have hlo : Asymptotics.IsLittleO Filter.atTop (fun n : ℕ => (n : ℝ) ^ 6)
      (fun n : ℕ => (64 : ℝ) ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt 6 (by norm_num)
  have hfun : (fun n : ℕ => 2 ^ 30 * (n : ℝ) ^ 6 * rfac * (Dm / γ) ^ 2
        * (Real.log (1 + Dm / γ) + Real.log (2 / rho)) / rho ^ 2)
      = fun n : ℕ => (2 ^ 30 * rfac * (Dm / γ) ^ 2
          * (Real.log (1 + Dm / γ) + Real.log (2 / rho)) / rho ^ 2) * (n : ℝ) ^ 6 := by
    funext n
    ring
  rw [hfun]
  exact (hlo.const_mul_left _).trans_isBigO hbig

/-! ## 7. Non-vacuity (`CLAUDE.md` §11)

A price theorem quantified over unsatisfiable hypotheses proves nothing.  Each witness
below exhibits concrete geometry, a concrete `t` satisfying the step-count hypothesis, and
a **positive** charged price. -/

section Witness

/-- **The hypothesis bundle of `Ttc.SamplerCost.drawOpCharge_le_poly` is satisfiable, at a
price that is a genuine positive natural.**

`n = 2`, `γ = 1`, `Dm = 2`, `ρ = 1`, `rfac = 1`, `t = 1`.  The step-count hypothesis holds
because the closed form is `(nonneg)/(φ²) + 1 ≥ 1`, and the price is
`drawOpCharge 1 2 1 = (1+2)·⌈2⌉₊ = 6`. -/
theorem exists_nondegenerate_poly_price :
    ∃ (n : ℕ) (γ Dm rho rfac : ℝ) (t : ℕ),
      2 ≤ n ∧ 1 ≤ rfac ∧ 0 < γ ∧ 2 * γ ≤ Dm ∧ 0 < rho ∧ rho ≤ 1 ∧
      (t : ℝ) ≤ (2 * (n : ℝ) * Real.log (1 + Dm / γ) + 2 * Real.log (2 / rho))
          / (min (1 / 32 : ℝ)
              (1 / (8 * (Dm / γ)) * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) ^ 2 + 1 ∧
      0 < drawOpCharge t n rfac := by
  refine ⟨2, 1, 2, 1, 1, 1, le_refl 2, le_refl 1, one_pos, by norm_num, one_pos,
    le_refl 1, ?_, ?_⟩
  · have hl1 : (0 : ℝ) ≤ Real.log (1 + (2 : ℝ) / 1) := Real.log_nonneg (by norm_num)
    have hl2 : (0 : ℝ) ≤ Real.log (2 / (1 : ℝ)) := Real.log_nonneg (by norm_num)
    have hnum : (0 : ℝ) ≤ 2 * ((2 : ℕ) : ℝ) * Real.log (1 + (2 : ℝ) / 1)
        + 2 * Real.log (2 / (1 : ℝ)) := by
      push_cast
      linarith
    have hden : (0 : ℝ) ≤ (min (1 / 32 : ℝ)
        (1 / (8 * ((2 : ℝ) / 1)) * ((1 : ℝ) / (4 * ((2 : ℕ) : ℝ)))
          / (256 * ((2 : ℕ) : ℝ)))) ^ 2 := sq_nonneg _
    have hdiv : (0 : ℝ) ≤ (2 * ((2 : ℕ) : ℝ) * Real.log (1 + (2 : ℝ) / 1)
        + 2 * Real.log (2 / (1 : ℝ)))
        / (min (1 / 32 : ℝ)
            (1 / (8 * ((2 : ℝ) / 1)) * ((1 : ℝ) / (4 * ((2 : ℕ) : ℝ)))
              / (256 * ((2 : ℕ) : ℝ)))) ^ 2 := div_nonneg hnum hden
    push_cast
    push_cast at hdiv
    linarith
  · have hc : stepOpCharge 2 1 = 2 := by
      unfold stepOpCharge
      norm_num
    unfold drawOpCharge
    rw [hc]
    omega

/-- **The comparison regime is inhabited too**: at the geometry of
`Ttc.SamplerCost.drawOpCharge_le_mixStepsBound_at_dim_sixteen` there is a positive `t`
satisfying the step-count hypothesis, and the charged price at it is positive.

Together with that theorem this says: a *nonzero* polynomial price is below the exponential
one — the comparison is not won by pricing nothing. -/
theorem exists_nondegenerate_comparison :
    ∃ t : ℕ,
      0 < t ∧
      (t : ℝ) ≤ (2 * ((16 : ℕ) : ℝ) * Real.log (1 + (2 : ℝ) / 1) + 2 * Real.log (2 / (1 : ℝ)))
          / (min (1 / 32 : ℝ)
              (1 / (8 * ((2 : ℝ) / 1)) * ((1 : ℝ) / (4 * ((16 : ℕ) : ℝ)))
                / (256 * ((16 : ℕ) : ℝ)))) ^ 2 + 1 ∧
      0 < drawOpCharge t 16 1 := by
  refine ⟨1, one_pos, ?_, ?_⟩
  · have hl1 : (0 : ℝ) ≤ Real.log (1 + (2 : ℝ) / 1) := Real.log_nonneg (by norm_num)
    have hl2 : (0 : ℝ) ≤ Real.log (2 / (1 : ℝ)) := Real.log_nonneg (by norm_num)
    have hnum : (0 : ℝ) ≤ 2 * ((16 : ℕ) : ℝ) * Real.log (1 + (2 : ℝ) / 1)
        + 2 * Real.log (2 / (1 : ℝ)) := by
      push_cast
      linarith
    have hdiv : (0 : ℝ) ≤ (2 * ((16 : ℕ) : ℝ) * Real.log (1 + (2 : ℝ) / 1)
        + 2 * Real.log (2 / (1 : ℝ)))
        / (min (1 / 32 : ℝ)
            (1 / (8 * ((2 : ℝ) / 1)) * ((1 : ℝ) / (4 * ((16 : ℕ) : ℝ)))
              / (256 * ((16 : ℕ) : ℝ)))) ^ 2 := div_nonneg hnum (sq_nonneg _)
    push_cast
    push_cast at hdiv
    linarith
  · have hc : stepOpCharge 16 1 = 16 := by
      unfold stepOpCharge
      norm_num
    unfold drawOpCharge
    rw [hc]
    omega

end Witness

end Ttc.SamplerCost

/-! ## Axiom profile

Target for every line: `[propext, Classical.choice, Quot.sound]`.

What `#print axioms` **cannot** see, and what the module docstring says instead: the step
count is a *hypothesis* here (no walk is proved to mix in this file), and
`Ttc.SamplerCost.stepOpCharge` remains a modelling `def` that measures no executable. -/

#print axioms Ttc.SamplerCost.speedyPhi_eq
#print axioms Ttc.SamplerCost.steps_arith_le
#print axioms Ttc.SamplerCost.speedySteps_le_poly
#print axioms Ttc.SamplerCost.speedySteps_rescaled_le_poly
#print axioms Ttc.SamplerCost.drawOpCharge_le_poly
#print axioms Ttc.SamplerCost.samplePrice_eq_drawOpCharge
#print axioms Ttc.SamplerCost.expTerm_le_mixStepsBound
#print axioms Ttc.SamplerCost.mixStepsBound_le_ttcSampPrice
#print axioms Ttc.SamplerCost.polyPrice_le_expTerm_at_dim_sixteen
#print axioms Ttc.SamplerCost.drawOpCharge_le_mixStepsBound_at_dim_sixteen
#print axioms Ttc.SamplerCost.polyPrice_isLittleO_mixStepsBound
#print axioms Ttc.SamplerCost.exists_nondegenerate_poly_price
#print axioms Ttc.SamplerCost.exists_nondegenerate_comparison
