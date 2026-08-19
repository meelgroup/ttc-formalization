/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.PriceList
import Ttc.Exec.CanonPolytope
import Ttc.Exec.Scale
import Ttc.Exec.CleanInput
import Ttc.Lattice.Transport

/-!
# `Exec/InflateBound`: the upper bound on `Vol(P'ᵢ)`, and the monotonicity that consumes it

`Ttc.mixStepsBound` (`Exec/SampleBound`) is the closed form for the sampler's chain length,
but the run evaluates it at three quantities that **move with the cube**: the inflated
body's diameter `Ttc.ttcSampDiam`, the warm-start ratio `Ttc.ttcSampWarm` and the tolerance
`Ttc.ttcSampTol`.  `Exec/PriceList` recorded that a *uniform* price for the sampler was
therefore blocked on an upper bound for `Vol(P'ᵢ)` — the volume of the Kannan–Vempala
inflated dilated polytope — which "this development proves none" of.

**This file proves it**, and then the three uniform bounds and the uniform price that
follow.

## §1  `Ttc.mixStepsBound` is monotone

```
mixStepsBound n γ Dm dl Mw eps
  = (log Mw + 2·log (1/eps)) · mixStepsGeom n γ Dm dl + 1
mixStepsGeom n γ Dm dl
  = 1024 · ((γ+Dm)/γ)^(2n) + 16384 · 4ⁿ · n² · Dm²/dl² · ((γ+Dm)/γ)^(4n)
```

`Ttc.mixStepsGeom` is increasing in `Dm` (`Ttc.mixStepsGeom_mono_Dm`) and nonnegative
(`Ttc.mixStepsGeom_nonneg`), the logarithmic factor is increasing in `Mw` and **decreasing
in `eps`**, so:

* `Ttc.mixStepsBound_mono_Dm` — increasing in `Dm`;
* `Ttc.mixStepsBound_mono_Mw` — increasing in `Mw`;
* `Ttc.mixStepsBound_anti_eps` — **decreasing** in `eps`;
* `Ttc.mixStepsBound_mono` — all three, in the shape a substitution needs.

**The `eps` direction is the one that inverts silently.**  `eps` occurs only inside
`log (1/eps)`, so a *smaller* `eps` gives a *larger* bound.  Since `epsᵢ = ε'/(4·Vol P'ᵢ)`
*shrinks* as `Vol P'ᵢ` grows, an **upper** bound on `Vol P'ᵢ` yields a **lower** bound on
`epsᵢ`, and it is the lower bound that `Ttc.mixStepsBound_mono` consumes.  A bound built
from an upper bound on `epsᵢ` would be false.

## §2  The volume bound

`Arlib.KV97.volume_inflated_le` gives `Vol P' ≤ (1 + κ/γ)ⁿ · Vol(body)` for a body with an
inscribed ball of radius `γ > 0`.  `Ttc.canon_body_eq_smul_region` identifies the canonical
body of cube `i` with `10^ρ · region M i` — an *equality* — and `Ttc.region_subset_sol`
plus measure monotonicity replaces `region M i` by `Sol(φ)`.  So
(`Ttc.toReal_volume_canonInflated_le`)

```
Vol(P'ᵢ) ≤ (1 + κ/(10^ρ·γ))ⁿ · (10^(ρn) · volSol M φ)      for every cube i of a DNF of φ,
```

the right-hand side naming no cube.  This is the same move `Exec/PriceList` made for the
volume oracle with `Ttc.region_subset_sol` and `Metric.diam_mono`; here it is measure
monotonicity instead of `Metric.diam_mono`.

**On the objection that this is circular.**  It is not.  `Ttc.volSol (atomSet atoms) φ` is a
function of the *input*, exactly as `Metric.diam (sol …)` — which the already-substituted
`cVol` price contains — is.  A cost bound in terms of the input's own volume is a closed
form, not a use of the quantity being estimated.

## §3  At the run's own data, and back to the user's `Vol(F)`

`Ttc.ttcSampVolPrice` is that bound at the run's cubes.  Two further steps take it all the
way back to the *user's* input: `Ttc.volSol_scaleAtoms` undoes the dilation `q`, and
`Ttc.volSol_preprocess` (proved here from `Ttc.volSol_pruneForm` and
`Ttc.volSol_cleanForm`) undoes both preprocessing passes, so

```
ttcSampVolPrice = (1 + κ/(10^ρ·q·γ̂))ⁿ · 10^(ρn) · qⁿ · Vol(F),
```

a closed expression in the **user's own** `Vol(F)` and the algorithm's own constants.  Every
name in it is defined under `Ttc/Model/` — `Ttc.algBlock`, `Ttc.algPrec`, `Ttc.algScale`,
`Ttc.algGamma`, `Ttc.canonRfac`, `Ttc.latticeScale`, `Ttc.volSol`, `Ttc.atomSet`,
`Ttc.preprocess`, `Ttc.toDNFd` — plus `Arlib.KV97.kappaOf`/`cOf`.

The other two uniform bounds follow:

| quantity | uniform bound | direction | lemma |
| --- | --- | --- | --- |
| `Ttc.ttcSampDiam … i` | `Ttc.ttcSampDiamPrice` | `≤` | `Ttc.ttcSampDiam_le` |
| `Ttc.ttcSampWarm … i` | `Ttc.ttcSampWarmPrice` | `≤` | `Ttc.ttcSampWarm_le` |
| `Ttc.ttcSampTol … i` | `Ttc.ttcSampTolPrice` | **`≥`** | `Ttc.ttcSampTolPrice_le` |

The diameter one is `Ttc.canonDm_le_diam_smul_sol`, again `Ttc.region_subset_sol` and
`Metric.diam_mono`; the warmness one additionally uses that a ball's Haar measure does not
depend on its centre (`MeasureTheory.Measure.addHaar_ball_center`), which is what removes
the cube from the denominator.

## §4  The uniform price

`Ttc.ttcSampStepsPrice` is `Ttc.mixStepsBound` at the three uniform values, and
`Ttc.ttcSampleSteps_le_ttcSampStepsPrice` proves it dominates **every** cube's step count.
It is the `cSample` analogue of `Ttc.ttcVolPrice`.

## What this does and does not repair

Nothing here changes the three undercounts `Exec/PriceList` lists, and they are not made
smaller by a uniform price:

* `Ttc.kv97SampD`'s **rejection rounds are unbounded and uncounted**;
* the **`while` loops of `alg:ttc` lines 32–42 are uncharged**;
* `Ttc.mixSteps` **does not occur in `Ttc.ttcEstimate`'s definitional closure** — it enters
  through `Ttc.ttcRates`, the *law*.  So this prices the chain the sampler's law is defined
  by, not steps the modelled run takes.

And the price is **exponential in `n`** twice over: `Ttc.mixStepsBound` carries
`4ⁿ·((γ+Dm)/γ)^(4n)`, and `Ttc.ttcSampVolPrice` carries `(1 + κ/(10^ρ·γ))ⁿ · 10^(ρn) · qⁿ`.
Two hypotheses of the final theorem are **not** discharged here and are stated, not hidden:
`1 ≤ Ttc.ttcSampWarm … i` (a warmness is at least one) and `Ttc.ttcSampTol … i ≤ 1` — both
are already binders of `Ttc.ttcSampleSteps_le` in `Exec/SampleBound`.

No `Ttc/Model/` file is touched, and no `def` here asserts anything: `Ttc.mixStepsGeom` and
the five `ttcSamp*Price`s are closed expressions, each tied to what it bounds by a proved
lemma.
-/

namespace Ttc

open MeasureTheory Set Pointwise

/-! # §1  `Ttc.mixStepsBound` is monotone in its three moving arguments -/

/-- **The geometric factor of `Ttc.mixStepsBound`** — everything the bound contains
except the logarithmic factor and the `+1`.  A closed expression, tied to
`Ttc.mixStepsBound` by `Ttc.mixStepsBound_eq` (`rfl`); it asserts nothing. -/
noncomputable def mixStepsGeom (n : ℕ) (γ Dm dl : ℝ) : ℝ :=
  1024 * ((γ + Dm) / γ) ^ (2 * n)
    + 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2 * ((γ + Dm) / γ) ^ (4 * n)

/-- `Ttc.mixStepsBound = (log Mw + 2·log(1/eps)) · Ttc.mixStepsGeom + 1`, by `rfl`. -/
theorem mixStepsBound_eq (n : ℕ) (γ Dm dl Mw eps : ℝ) :
    mixStepsBound n γ Dm dl Mw eps
      = (Real.log Mw + 2 * Real.log (1 / eps)) * mixStepsGeom n γ Dm dl + 1 := rfl

/-- **The geometric factor is nonnegative** — needed everywhere below, because a
monotone step in the *logarithmic* factor may only be multiplied through by
something nonnegative.  `0 < γ` and `0 ≤ Dm` are exactly what make the base
`(γ+Dm)/γ` of both exponentials nonnegative. -/
theorem mixStepsGeom_nonneg {n : ℕ} {γ Dm dl : ℝ} (hγ : 0 < γ) (hDm : 0 ≤ Dm) :
    0 ≤ mixStepsGeom n γ Dm dl := by
  have hb : (0 : ℝ) ≤ (γ + Dm) / γ := div_nonneg (by linarith) hγ.le
  have h1 : (0 : ℝ) ≤ 1024 * ((γ + Dm) / γ) ^ (2 * n) :=
    mul_nonneg (by norm_num) (pow_nonneg hb _)
  have hc : (0 : ℝ) ≤ 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2
      * ((γ + Dm) / γ) ^ (4 * n) := mul_nonneg hc (pow_nonneg hb _)
  simp only [mixStepsGeom]
  linarith

/-- **The geometric factor is increasing in the diameter.**  Both summands are:
`((γ+Dm)/γ)^k` because the base grows and is nonnegative, and `Dm²/dl²` because
`Dm ↦ Dm²` is monotone on `[0, ∞)`. -/
theorem mixStepsGeom_mono_Dm {n : ℕ} {γ Dm₁ Dm₂ dl : ℝ} (hγ : 0 < γ) (hDm0 : 0 ≤ Dm₁)
    (hDm : Dm₁ ≤ Dm₂) : mixStepsGeom n γ Dm₁ dl ≤ mixStepsGeom n γ Dm₂ dl := by
  have hb1 : (0 : ℝ) ≤ (γ + Dm₁) / γ := div_nonneg (by linarith) hγ.le
  have hble : (γ + Dm₁) / γ ≤ (γ + Dm₂) / γ :=
    div_le_div_of_nonneg_right (by linarith) hγ.le
  have h2n : ((γ + Dm₁) / γ) ^ (2 * n) ≤ ((γ + Dm₂) / γ) ^ (2 * n) :=
    pow_le_pow_left₀ hb1 hble _
  have h4n : ((γ + Dm₁) / γ) ^ (4 * n) ≤ ((γ + Dm₂) / γ) ^ (4 * n) :=
    pow_le_pow_left₀ hb1 hble _
  have hcoef : (0 : ℝ) ≤ 16384 * 4 ^ n * (n : ℝ) ^ 2 := by positivity
  have hsq : Dm₁ ^ 2 ≤ Dm₂ ^ 2 := by nlinarith
  have hnum : 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm₁ ^ 2
      ≤ 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm₂ ^ 2 := mul_le_mul_of_nonneg_left hsq hcoef
  have hc12 : 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm₁ ^ 2 / dl ^ 2
      ≤ 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm₂ ^ 2 / dl ^ 2 :=
    div_le_div_of_nonneg_right hnum (sq_nonneg dl)
  have hc1 : (0 : ℝ) ≤ 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm₁ ^ 2 / dl ^ 2 := by positivity
  have hprod : 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm₁ ^ 2 / dl ^ 2 * ((γ + Dm₁) / γ) ^ (4 * n)
      ≤ 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm₂ ^ 2 / dl ^ 2 * ((γ + Dm₂) / γ) ^ (4 * n) :=
    mul_le_mul hc12 h4n (pow_nonneg hb1 _) (le_trans hc1 hc12)
  simp only [mixStepsGeom]
  linarith

/-- **The logarithmic factor is nonnegative** for a warmness `≥ 1` and a tolerance
in `(0,1]` — the same side conditions `Ttc.mixSteps_le` already carries. -/
theorem mixStepsLog_nonneg {Mw eps : ℝ} (hMw : 1 ≤ Mw) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    0 ≤ Real.log Mw + 2 * Real.log (1 / eps) := by
  have h1 : 0 ≤ Real.log Mw := Real.log_nonneg hMw
  have h2 : 0 ≤ Real.log (1 / eps) := Real.log_nonneg ((one_le_div heps0).2 heps1)
  linarith

/-- **Increasing in the diameter `Dm`.**  Side conditions: `0 < γ`, `0 ≤ Dm₁`, and
nonnegativity of the logarithmic factor (`1 ≤ Mw`, `0 < eps ≤ 1`). -/
theorem mixStepsBound_mono_Dm {n : ℕ} {γ Dm₁ Dm₂ dl Mw eps : ℝ} (hγ : 0 < γ)
    (hDm0 : 0 ≤ Dm₁) (hDm : Dm₁ ≤ Dm₂) (hMw : 1 ≤ Mw) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    mixStepsBound n γ Dm₁ dl Mw eps ≤ mixStepsBound n γ Dm₂ dl Mw eps := by
  simp only [mixStepsBound_eq]
  have := mul_le_mul_of_nonneg_left (mixStepsGeom_mono_Dm (n := n) (dl := dl) hγ hDm0 hDm)
    (mixStepsLog_nonneg hMw heps0 heps1)
  linarith

/-- **Increasing in the warm-start ratio `Mw`.**  Side conditions: `0 < γ`, `0 ≤ Dm`
(so the geometric factor is nonnegative) and `0 < Mw₁` (so `Real.log` is monotone
there). -/
theorem mixStepsBound_mono_Mw {n : ℕ} {γ Dm dl Mw₁ Mw₂ eps : ℝ} (hγ : 0 < γ)
    (hDm0 : 0 ≤ Dm) (hMw0 : 0 < Mw₁) (hMw : Mw₁ ≤ Mw₂) :
    mixStepsBound n γ Dm dl Mw₁ eps ≤ mixStepsBound n γ Dm dl Mw₂ eps := by
  simp only [mixStepsBound_eq]
  have hlog : Real.log Mw₁ ≤ Real.log Mw₂ := Real.log_le_log hMw0 hMw
  have := mul_le_mul_of_nonneg_right
    (by linarith : Real.log Mw₁ + 2 * Real.log (1 / eps)
      ≤ Real.log Mw₂ + 2 * Real.log (1 / eps))
    (mixStepsGeom_nonneg (n := n) (dl := dl) hγ hDm0)
  linarith

/-- **Decreasing in the tolerance `eps`** — the direction that is easy to invert and
must not be.  `eps` enters only as `log (1/eps)`, so a *smaller* `eps` gives a
*larger* bound; consequently a *lower* bound on `eps` is what an upper bound on the
mixing time needs.  Side conditions: `0 < γ`, `0 ≤ Dm`, `0 < eps₁ ≤ eps₂`. -/
theorem mixStepsBound_anti_eps {n : ℕ} {γ Dm dl Mw eps₁ eps₂ : ℝ} (hγ : 0 < γ)
    (hDm0 : 0 ≤ Dm) (heps0 : 0 < eps₁) (heps : eps₁ ≤ eps₂) :
    mixStepsBound n γ Dm dl Mw eps₂ ≤ mixStepsBound n γ Dm dl Mw eps₁ := by
  simp only [mixStepsBound_eq]
  have heps2 : 0 < eps₂ := lt_of_lt_of_le heps0 heps
  have hinv : 1 / eps₂ ≤ 1 / eps₁ := one_div_le_one_div_of_le heps0 heps
  have hlog : Real.log (1 / eps₂) ≤ Real.log (1 / eps₁) :=
    Real.log_le_log (by positivity) hinv
  have := mul_le_mul_of_nonneg_right
    (by linarith : Real.log Mw + 2 * Real.log (1 / eps₂)
      ≤ Real.log Mw + 2 * Real.log (1 / eps₁))
    (mixStepsGeom_nonneg (n := n) (dl := dl) hγ hDm0)
  linarith

/-- **All three at once: the substitution lemma.**

Given an upper bound `DmU` on the diameter, an upper bound `MwU` on the warmness and
a **lower** bound `epsL` on the tolerance, the bound at the actual data is at most
the bound at the three uniform values.  This is the shape a uniform price needs:
`Ttc.mixStepsBound n γ DmU dl MwU epsL` mentions no cube.

Side conditions, all of them used: `0 < γ`; `0 ≤ Dm ≤ DmU`; `1 ≤ Mw ≤ MwU`;
`0 < epsL ≤ eps ≤ 1`. -/
theorem mixStepsBound_mono {n : ℕ} {γ Dm DmU dl Mw MwU eps epsL : ℝ} (hγ : 0 < γ)
    (hDm0 : 0 ≤ Dm) (hDmU : Dm ≤ DmU) (hMw : 1 ≤ Mw) (hMwU : Mw ≤ MwU)
    (hepsL : 0 < epsL) (hepsLe : epsL ≤ eps) (heps1 : eps ≤ 1) :
    mixStepsBound n γ Dm dl Mw eps ≤ mixStepsBound n γ DmU dl MwU epsL := by
  have hDmU0 : 0 ≤ DmU := le_trans hDm0 hDmU
  have heps0 : 0 < eps := lt_of_lt_of_le hepsL hepsLe
  calc mixStepsBound n γ Dm dl Mw eps
      ≤ mixStepsBound n γ DmU dl Mw eps :=
        mixStepsBound_mono_Dm hγ hDm0 hDmU hMw heps0 heps1
    _ ≤ mixStepsBound n γ DmU dl MwU eps :=
        mixStepsBound_mono_Mw hγ hDmU0 (lt_of_lt_of_le zero_lt_one hMw) hMwU
    _ ≤ mixStepsBound n γ DmU dl MwU epsL :=
        mixStepsBound_anti_eps hγ hDmU0 hepsL hepsLe

/-! # §2  A uniform upper bound on `Vol(P'ᵢ)`

Nothing in this section mentions the run: it is `Arlib.KV97.volume_inflated_le` composed
with `Ttc.canon_body_eq_smul_region` and `Ttc.region_subset_sol`, which is the same route
`Exec/PriceList` §1 took for the volume oracle. -/

variable {A : Type*} {n : ℕ}

/-- **The dilated inscribed ball sits inside the canonical body.**  The body *is* the
dilated region (`Ttc.canon_body_eq_smul_region`), and a ball of radius `γ` inside the
region becomes one of radius `10^ρ·γ` inside the dilate (`Ttc.ball_radius_scales`). -/
theorem ball_subset_canon_body (atoms : A → LinAtom n) {D : DNF A}
    (hDpos : DNF.IsPositive D) (ρ : ℤ) {γ : ℝ}
    (cen : {c : Cube A // c ∈ D} → Space n)
    (hball : ∀ i : {c : Cube A // c ∈ D},
      Metric.ball (cen i) γ ⊆ region (atomSet atoms) i.val)
    (i : {c : Cube A // c ∈ D}) :
    Metric.ball (latticeScale ρ • cen i) (latticeScale ρ * γ)
      ⊆ Arlib.Polytope.body (canonAm atoms D i) (canonBv atoms D (latticeScale ρ) i) := by
  rw [canon_body_eq_smul_region atoms hDpos (latticeScale_pos ρ) i]
  exact ball_radius_scales (latticeScale_pos ρ) _ _ (hball i)

/-- **The canonical body has finite volume.**  `Arlib.KV97`'s finiteness hypotheses are
genuine (an unbounded polytope has infinite volume), and this is where they are
discharged: the body is the dilate of a region of a DNF of `φ`, which is inside `Sol(φ)`,
which is bounded. -/
theorem volume_canon_body_ne_top (atoms : A → LinAtom n) {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hDpos : DNF.IsPositive D)
    (hb : Bornology.IsBounded (sol (atomSet atoms) φ)) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) :
    volume (Arlib.Polytope.body (canonAm atoms D i)
      (canonBv atoms D (latticeScale ρ) i)) ≠ ⊤ := by
  rw [canon_body_eq_smul_region atoms hDpos (latticeScale_pos ρ) i]
  exact ((hb.smul₀ _).subset
    (Set.smul_set_mono (region_subset_sol hD i.property))).measure_lt_top.ne

/-- **The canonical body's volume, bounded by the input's own volume.**

`Vol(bodyᵢ) ≤ 10^(ρn) · volSol M φ` — the cube appears only on the left.  This is
`Ttc.region_subset_sol` under `MeasureTheory.measure_mono`, transported through the
dilation by `Ttc.volume_smul_body`. -/
theorem toReal_volume_canon_body_le (atoms : A → LinAtom n) {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hDpos : DNF.IsPositive D)
    (hb : Bornology.IsBounded (sol (atomSet atoms) φ)) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) :
    (volume (Arlib.Polytope.body (canonAm atoms D i)
        (canonBv atoms D (latticeScale ρ) i))).toReal
      ≤ latticeScale ρ ^ n * volSol (atomSet atoms) φ := by
  have hs : (0 : ℝ) < latticeScale ρ := latticeScale_pos ρ
  rw [canon_body_eq_smul_region atoms hDpos hs i, volume_smul_body hs.le,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.le n)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hs.le n)
  exact ENNReal.toReal_mono hb.measure_lt_top.ne
    (measure_mono (region_subset_sol hD i.property))

/-- **The Kannan–Vempala inflated dilated cube body, bounded by the input's own
volume — uniformly over the cubes.**

```
Vol(P'ᵢ) ≤ (1 + κ/(10^ρ·γ))ⁿ · (10^(ρn) · volSol M φ)
```

`Arlib.KV97.volume_inflated_le` bounds `Vol(P'ᵢ)` by `(1 + κ/γ)ⁿ · Vol(bodyᵢ)` — its
three hypotheses being discharged here by `Ttc.ball_subset_canon_body` (the inscribed
ball, dilated), `Arlib.KV97.cOf_nonneg`-style nonnegativity of the inflation constant,
and `Ttc.volume_canon_body_ne_top` (finiteness) — and `Ttc.toReal_volume_canon_body_le`
finishes.  **The right-hand side does not mention `i`.** -/
theorem toReal_volume_canonInflated_le (atoms : A → LinAtom n) {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hDpos : DNF.IsPositive D)
    (hb : Bornology.IsBounded (sol (atomSet atoms) φ)) (ρ : ℤ) {γ : ℝ} (hγ : 0 < γ)
    (cen : {c : Cube A // c ∈ D} → Space n)
    (hball : ∀ i : {c : Cube A // c ∈ D},
      Metric.ball (cen i) γ ⊆ region (atomSet atoms) i.val)
    {cst r : ℝ} (hcst : 0 ≤ cst) (i : {c : Cube A // c ∈ D}) :
    (volume (Arlib.KV97.inflated (canonAm atoms D i)
        (canonBv atoms D (latticeScale ρ) i) cst r)).toReal
      ≤ (1 + Arlib.KV97.kappaOf cst r / (latticeScale ρ * γ)) ^ n
          * (latticeScale ρ ^ n * volSol (atomSet atoms) φ) := by
  have hs : (0 : ℝ) < latticeScale ρ := latticeScale_pos ρ
  have key := Arlib.KV97.toReal_volume_inflated_le (r := r) (mul_pos hs hγ) hcst
    (ball_subset_canon_body atoms hDpos ρ cen hball i)
    (volume_canon_body_ne_top atoms hD hDpos hb ρ i)
  have hk : (0 : ℝ) ≤ 1 + Arlib.KV97.kappaOf cst r / (latticeScale ρ * γ) := by
    have := div_nonneg (Arlib.KV97.kappaOf_nonneg (r := r) hcst) (mul_pos hs hγ).le
    linarith
  exact key.trans (mul_le_mul_of_nonneg_left
    (toReal_volume_canon_body_le atoms hD hDpos hb ρ i) (pow_nonneg hk n))

/-- **`Vol(P'ᵢ) > 0`** — the inflated body contains the dilated inscribed ball, which is
open and nonempty, and it has finite volume.  This is what makes `Ttc.ttcSampTol`'s
division by `Vol(P'ᵢ)` legitimate rather than an `x / 0 = 0` artefact. -/
theorem toReal_volume_canonInflated_pos (atoms : A → LinAtom n) {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hDpos : DNF.IsPositive D)
    (hb : Bornology.IsBounded (sol (atomSet atoms) φ)) (ρ : ℤ) {γ : ℝ} (hγ : 0 < γ)
    (cen : {c : Cube A // c ∈ D} → Space n)
    (hball : ∀ i : {c : Cube A // c ∈ D},
      Metric.ball (cen i) γ ⊆ region (atomSet atoms) i.val)
    {cst r : ℝ} (hcst : 0 ≤ cst) (i : {c : Cube A // c ∈ D}) :
    0 < (volume (Arlib.KV97.inflated (canonAm atoms D i)
      (canonBv atoms D (latticeScale ρ) i) cst r)).toReal :=
  Arlib.KV97.toReal_volume_inflated_pos (r := r) (mul_pos (latticeScale_pos ρ) hγ) hcst
    (ball_subset_canon_body atoms hDpos ρ cen hball i)
    (volume_canon_body_ne_top atoms hD hDpos hb ρ i)

/-- **The uniform diameter bound for the *un*inflated dilated cube body.**
`Ttc.canonDm` is `Metric.diam (10^ρ · region M i)`, and `Ttc.region_subset_sol` plus
`Metric.diam_mono` widen it to the dilated solution set — the same step
`Ttc.diam_region_le_diam_sol` (`Exec/PriceList`) makes for the volume oracle. -/
theorem canonDm_le_diam_smul_sol {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hb : Bornology.IsBounded (sol M φ)) (ρ : ℤ)
    (i : {c : Cube A // c ∈ D}) :
    canonDm M D ρ i ≤ Metric.diam (latticeScale ρ • sol M φ) :=
  Metric.diam_mono (Set.smul_set_mono (region_subset_sol hD i.property)) (hb.smul₀ _)

/-! # §3  At the run's own data

Everything below is §2 at `Ttc.algAtoms`, `Ttc.algCen`, `Ttc.algGamma` and
`Ttc.algPrec` — the `Model/` spellings of the run's dilated input, centres, inscribed
radius and precision — with the three hypotheses `Exec/PriceList` §2 already discharges
(`Ttc.ball_subset_region_algAtoms`, `Ttc.isBounded_sol_algAtoms`, `Ttc.algGamma_pos`). -/

section AtTheRun

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The dilation `q` is positive** — `Ttc.runScale_pos` at the run's own data, the same
term `Ttc.algGamma_pos` (`Exec/PriceList`) is built from. -/
theorem algScale_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : 0 < algScale atoms φ ε δ :=
  runScale_pos atoms (preprocess atoms φ) ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
    (ttcInput_bdd atoms φ hφ hpos) (autoGamma atoms (preprocess atoms φ))

/-- **Preprocessing moves neither `Sol(F)`'s volume.**  `Ttc.volSol_pruneForm` (pruning
deletes only measure-zero cubes) then `Ttc.volSol_cleanForm` (cleaning is a set
equality); the two side conditions are `Ttc.pruneNeNil` and
`Ttc.cleanDNF_ne_nil_of_interior` at `Ttc.pruneInt`, both from `hφ` and `hpos` alone.

This is what lets `Ttc.ttcSampVolPrice` be written against the **user's own** `Vol(F)`. -/
theorem volSol_preprocess (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) :
    volSol (atomSet atoms) (preprocess atoms φ) = volSol (atomSet atoms) φ := by
  show volSol (atomSet atoms) (cleanForm atoms (pruneForm atoms φ)) = _
  rw [volSol_cleanForm atoms (isPositive_pruneForm atoms φ)
      (cleanDNF_ne_nil_of_interior atoms (isPositive_pruneForm atoms φ)
        (pruneInt atoms hφ hpos)),
    volSol_pruneForm atoms hφ (pruneNeNil atoms hpos)]

/-- **The dilated preprocessed volume, in terms of the user's own `Vol(F)`**:
`qⁿ · Vol(F)`.  `Ttc.volSol_scaleAtoms` undoes the dilation and
`Ttc.volSol_preprocess` undoes both preprocessing passes. -/
theorem volSol_algAtoms (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    volSol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)
      = algScale atoms φ ε δ ^ n * volSol (atomSet atoms) φ := by
  show volSol (atomSet (scaleAtoms (algScale atoms φ ε δ) atoms)) (preprocess atoms φ) = _
  rw [volSol_scaleAtoms (algScale_pos atoms φ ε δ hε0 hε1 hn hφ hpos) atoms
      (preprocess atoms φ),
    volSol_preprocess atoms φ hφ hpos]

/-- **The run's Kannan–Vempala displacement `κ`** — `κ = c + √(2 log r)` at `c = cOf ε'`
and `r` the facet count.  An abbreviation for a sub-expression of `Ttc.ttcSampInradius`
and `Ttc.ttcSampDiam`; `Ttc.ttcSampInradius_eq` pins it. -/
noncomputable def ttcSampKappa : ℝ :=
  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
    (canonRfac (toDNFd (preprocess atoms φ)))

theorem ttcSampInradius_eq :
    ttcSampInradius atoms φ ε δ = ttcSampStep atoms φ ε δ + ttcSampKappa atoms φ ε δ := rfl

/-- The same, spelled out: every name below is defined under `Ttc/Model/`, apart from
`Arlib.KV97.kappaOf`/`cOf`.  This is the form a headline statement can carry. -/
theorem ttcSampInradius_model :
    ttcSampInradius atoms φ ε δ
      = latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ
        + Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
            (canonRfac (toDNFd (preprocess atoms φ))) := rfl

theorem ttcSampStep_eq :
    ttcSampStep atoms φ ε δ = latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ :=
  rfl

/-- `0 ≤ κ` — `Arlib.KV97.kappaOf_nonneg` at `Arlib.KV97.cOf_nonneg`, which is
unconditional. -/
theorem ttcSampKappa_nonneg : 0 ≤ ttcSampKappa atoms φ ε δ :=
  Arlib.KV97.kappaOf_nonneg Arlib.KV97.cOf_nonneg

/-- **The ball-walk step `10^ρ·q·γ̂` is positive** — `Ttc.latticeScale_pos` and
`Ttc.algGamma_pos` (`Exec/PriceList`). -/
theorem ttcSampStep_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : 0 < ttcSampStep atoms φ ε δ :=
  mul_pos (latticeScale_pos _) (algGamma_pos atoms φ ε δ hε0 hε1 hn hφ hpos)

/-- **The inflation factor `1 + κ/(10^ρ·q·γ̂)` is at least one.** -/
theorem one_le_ttcSampFactor (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    1 ≤ 1 + ttcSampKappa atoms φ ε δ / ttcSampStep atoms φ ε δ := by
  have := div_nonneg (ttcSampKappa_nonneg atoms φ ε δ)
    (ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos).le
  linarith

/-! ## The uniform price for `Vol(P'ᵢ)` -/

/-- **The uniform upper bound on the inflated body's volume**, in the **user's own**
`Vol(F)`:

```
ttcSampVolPrice = (1 + κ/(10^ρ·q·γ̂))ⁿ · (10^(ρn) · (qⁿ · Vol(F)))
```

Every name is defined under `Ttc/Model/` (`Ttc.algBlock`, `Ttc.algPrec`, `Ttc.algScale`,
`Ttc.algGamma`, `Ttc.canonRfac`, `Ttc.toDNFd`, `Ttc.preprocess`, `Ttc.volSol`,
`Ttc.atomSet`, `Ttc.latticeScale`) except `Arlib.KV97.kappaOf`/`cOf`, so it can be carried
in a headline statement.

The name promises a semantic identity — "an upper bound on the volume the sampler's
inflated body has" — and `Ttc.toReal_volume_ttcSampBody_le` proves it.

**Exponential in `n`** three times over: `(1+κ/…)ⁿ`, `10^(ρn)` and `qⁿ`. -/
noncomputable def ttcSampVolPrice : ℝ :=
  (1 + ttcSampKappa atoms φ ε δ / ttcSampStep atoms φ ε δ) ^ n
    * (latticeScale (algPrec atoms φ ε δ) ^ n
        * (algScale atoms φ ε δ ^ n * volSol (atomSet atoms) φ))

theorem ttcSampVolPrice_def :
    ttcSampVolPrice atoms φ ε δ
      = (1 + ttcSampKappa atoms φ ε δ / ttcSampStep atoms φ ε δ) ^ n
          * (latticeScale (algPrec atoms φ ε δ) ^ n
              * (algScale atoms φ ε δ ^ n * volSol (atomSet atoms) φ)) := rfl

/-- **The volume price, spelled out in `Ttc/Model/` vocabulary.**

```
ttcSampVolPrice
  = (1 + κ / (10^ρ · q·γ̂))ⁿ · (10^(ρn) · (qⁿ · Vol(F)))
κ = Arlib.KV97.kappaOf (Arlib.KV97.cOf ε') r,  r = canonRfac (toDNFd (preprocess atoms φ))
```

Every `Ttc` name here — `Ttc.algBlock`, `Ttc.algPrec`, `Ttc.algGamma`, `Ttc.algScale`,
`Ttc.canonRfac`, `Ttc.toDNFd`, `Ttc.preprocess`, `Ttc.latticeScale`, `Ttc.volSol`,
`Ttc.atomSet` — is defined under `Ttc/Model/`, so this expression may be carried in a
headline statement exactly as `Ttc.ttcVolPrice`'s body is.  Proved by `rfl`. -/
theorem ttcSampVolPrice_model :
    ttcSampVolPrice atoms φ ε δ
      = (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
              (canonRfac (toDNFd (preprocess atoms φ)))
            / (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) ^ n
          * (latticeScale (algPrec atoms φ ε δ) ^ n
              * (algScale atoms φ ε δ ^ n * volSol (atomSet atoms) φ)) := rfl

/-- **The price dominates the inflated body's volume, at every cube.**  §2 at the run's
own data, with `Ttc.volSol_algAtoms` used to rewrite the dilated preprocessed volume as
`qⁿ · Vol(F)`. -/
theorem toReal_volume_ttcSampBody_le (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    (volume (ttcSampBody atoms φ ε δ i)).toReal ≤ ttcSampVolPrice atoms φ ε δ := by
  have h := toReal_volume_canonInflated_le (algAtoms atoms φ ε δ)
    (toDNFd_isDNFOf (preprocess atoms φ))
    (toDNFd_isPositive (ttcInput_isPositive atoms φ))
    (isBounded_sol_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (algPrec atoms φ ε δ)
    (algGamma_pos atoms φ ε δ hε0 hε1 hn hφ hpos) (algCen atoms φ ε δ)
    (ball_subset_region_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
    (cst := Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
    (r := canonRfac (toDNFd (preprocess atoms φ))) Arlib.KV97.cOf_nonneg i
  rw [volSol_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos] at h
  exact h

/-- **The inflated body has positive volume, at every cube** — §2's positivity at the
run's data.  Needed for `Ttc.ttcSampTolPrice_le`, which divides by it. -/
theorem toReal_volume_ttcSampBody_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    0 < (volume (ttcSampBody atoms φ ε δ i)).toReal :=
  toReal_volume_canonInflated_pos (algAtoms atoms φ ε δ)
    (toDNFd_isDNFOf (preprocess atoms φ))
    (toDNFd_isPositive (ttcInput_isPositive atoms φ))
    (isBounded_sol_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (algPrec atoms φ ε δ)
    (algGamma_pos atoms φ ε δ hε0 hε1 hn hφ hpos) (algCen atoms φ ε δ)
    (ball_subset_region_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
    (cst := Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
    (r := canonRfac (toDNFd (preprocess atoms φ))) Arlib.KV97.cOf_nonneg i

/-- **The price is positive** — every factor is, `Vol(F) > 0` being `hpos`. -/
theorem ttcSampVolPrice_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : 0 < ttcSampVolPrice atoms φ ε δ := by
  have hf : (1 : ℝ) ≤ 1 + ttcSampKappa atoms φ ε δ / ttcSampStep atoms φ ε δ :=
    one_le_ttcSampFactor atoms φ ε δ hε0 hε1 hn hφ hpos
  have hq : 0 < algScale atoms φ ε δ := algScale_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  have hl : 0 < latticeScale (algPrec atoms φ ε δ) := latticeScale_pos _
  have hfp : 0 < (1 + ttcSampKappa atoms φ ε δ / ttcSampStep atoms φ ε δ) ^ n :=
    pow_pos (by linarith) n
  simp only [ttcSampVolPrice]
  have := mul_pos (pow_pos hq n) hpos
  have := mul_pos (pow_pos hl n) this
  exact mul_pos hfp this

/-! ## The three uniform bounds -/

/-- **The uniform diameter price** — `(1 + κ/(10^ρ·q·γ̂)) · diam(10^ρ · Sol)`, at the
dilated preprocessed solution set, which is the very set `Ttc.ttcVolPrice`
(`Exec/PriceList`) takes the diameter of. -/
noncomputable def ttcSampDiamPrice : ℝ :=
  (1 + ttcSampKappa atoms φ ε δ / ttcSampStep atoms φ ε δ)
    * Metric.diam (latticeScale (algPrec atoms φ ε δ)
        • sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))

/-- The diameter price in `Ttc/Model/` vocabulary, by `rfl`.  The set whose diameter it
takes is the dilate of the very set `Ttc.ttcVolPrice` (`Exec/PriceList`) measures the
diameter of. -/
theorem ttcSampDiamPrice_model :
    ttcSampDiamPrice atoms φ ε δ
      = (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
              (canonRfac (toDNFd (preprocess atoms φ)))
            / (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ))
          * Metric.diam (latticeScale (algPrec atoms φ ε δ)
              • sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)) := rfl

/-- **The diameter price dominates every cube's diameter.**
`Ttc.canonDm_le_diam_smul_sol`, scaled by the (nonnegative) inflation factor. -/
theorem ttcSampDiam_le (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    ttcSampDiam atoms φ ε δ i ≤ ttcSampDiamPrice atoms φ ε δ := by
  have hf : (1 : ℝ) ≤ 1 + ttcSampKappa atoms φ ε δ / ttcSampStep atoms φ ε δ :=
    one_le_ttcSampFactor atoms φ ε δ hε0 hε1 hn hφ hpos
  show (1 + ttcSampKappa atoms φ ε δ / ttcSampStep atoms φ ε δ)
      * canonDm (atomSet (algAtoms atoms φ ε δ)) (toDNFd (preprocess atoms φ))
          (algPrec atoms φ ε δ) i ≤ _
  exact mul_le_mul_of_nonneg_left
    (canonDm_le_diam_smul_sol (toDNFd_isDNFOf (preprocess atoms φ))
      (isBounded_sol_algAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) _ i) (by linarith)

/-- **Every cube's diameter is nonnegative** — `Metric.diam` is, and the inflation factor
is at least one.  This is `Ttc.mixStepsBound_mono`'s `hDm0`. -/
theorem ttcSampDiam_nonneg (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    0 ≤ ttcSampDiam atoms φ ε δ i := by
  have hf : (1 : ℝ) ≤ 1 + ttcSampKappa atoms φ ε δ / ttcSampStep atoms φ ε δ :=
    one_le_ttcSampFactor atoms φ ε δ hε0 hε1 hn hφ hpos
  show 0 ≤ (1 + ttcSampKappa atoms φ ε δ / ttcSampStep atoms φ ε δ)
      * canonDm (atomSet (algAtoms atoms φ ε δ)) (toDNFd (preprocess atoms φ))
          (algPrec atoms φ ε δ) i
  exact mul_nonneg (by linarith) Metric.diam_nonneg

/-- **The uniform warmness price** — the volume price over the volume of a ball of the
inflated inradius **at the origin**.  The run's own ratio has the ball at `10^ρ·cᵢ`, whose
centre moves with the cube; a Haar measure does not see a ball's centre
(`MeasureTheory.Measure.addHaar_ball_center`), which is what makes this uniform. -/
noncomputable def ttcSampWarmPrice : ℝ :=
  ttcSampVolPrice atoms φ ε δ
    / (volume (Metric.ball (0 : Space n) (ttcSampInradius atoms φ ε δ))).toReal

/-- **The warmness price dominates every cube's warmness.** -/
theorem ttcSampWarm_le (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    ttcSampWarm atoms φ ε δ i ≤ ttcSampWarmPrice atoms φ ε δ := by
  show (volume (ttcSampBody atoms φ ε δ i) /
      volume (Metric.ball (latticeScale (algPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
        (ttcSampInradius atoms φ ε δ))).toReal ≤ _
  rw [ENNReal.toReal_div, Measure.addHaar_ball_center]
  exact div_le_div_of_nonneg_right
    (toReal_volume_ttcSampBody_le atoms φ ε δ hε0 hε1 hn hφ hpos i) ENNReal.toReal_nonneg

/-- **The uniform tolerance price** — `ε'/(4 · ttcSampVolPrice)`.  This is a **lower**
bound on `Ttc.ttcSampTol`, not an upper one: the tolerance shrinks as the body grows, and
`Ttc.mixStepsBound` is *decreasing* in it. -/
noncomputable def ttcSampTolPrice : ℝ :=
  (algBlock atoms φ ε δ).epsPrime / (4 * ttcSampVolPrice atoms φ ε δ)

/-- **The tolerance price is a lower bound on every cube's tolerance** — note the
direction.  `Ttc.toReal_volume_ttcSampBody_pos` is what makes the division on the right
legitimate. -/
theorem ttcSampTolPrice_le (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    ttcSampTolPrice atoms φ ε δ ≤ ttcSampTol atoms φ ε δ i := by
  have hx : 0 < (volume (ttcSampBody atoms φ ε δ i)).toReal :=
    toReal_volume_ttcSampBody_pos atoms φ ε δ hε0 hε1 hn hφ hpos i
  have hle := toReal_volume_ttcSampBody_le atoms φ ε δ hε0 hε1 hn hφ hpos i
  have hnum : 0 ≤ (algBlock atoms φ ε δ).epsPrime :=
    (algBlock_epsPrime_pos atoms φ ε δ).le
  show (algBlock atoms φ ε δ).epsPrime / (4 * ttcSampVolPrice atoms φ ε δ)
      ≤ (algBlock atoms φ ε δ).epsPrime / (4 * (volume (ttcSampBody atoms φ ε δ i)).toReal)
  gcongr

/-- **The tolerance price is positive** — `ε' > 0` (`Ttc.algBlock_epsPrime_pos`) over a
positive volume price. -/
theorem ttcSampTolPrice_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : 0 < ttcSampTolPrice atoms φ ε δ := by
  have hV : 0 < ttcSampVolPrice atoms φ ε δ :=
    ttcSampVolPrice_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  have hε' : 0 < (algBlock atoms φ ε δ).epsPrime := algBlock_epsPrime_pos atoms φ ε δ
  simp only [ttcSampTolPrice]
  positivity

/-! # §4  The uniform price for `cSample` -/

/-- **The uniform per-sample price of the constructed sampler**:
`Ttc.mixStepsBound` at the inflated inradius, the ball-walk step, and the **three uniform
values** of §3 — `Ttc.ttcSampDiamPrice`, `Ttc.ttcSampWarmPrice` and
`Ttc.ttcSampTolPrice`.  It mentions no cube.

The name promises a semantic identity — "the price that dominates the steps the sampler's
chain takes at every cube" — and `Ttc.ttcSampleSteps_le_ttcSampStepsPrice` proves it.

**Exponential in `n`** — see `Exec/SampleBound`'s module docstring for
`Ttc.mixStepsBound`'s own `4ⁿ·((γ+Dm)/γ)^(4n)`, and this file's for the volume price's
three further exponentials. -/
noncomputable def ttcSampStepsPrice : ℝ :=
  mixStepsBound n (ttcSampInradius atoms φ ε δ) (ttcSampDiamPrice atoms φ ε δ)
    (ttcSampStep atoms φ ε δ) (ttcSampWarmPrice atoms φ ε δ) (ttcSampTolPrice atoms φ ε δ)

theorem ttcSampStepsPrice_def :
    ttcSampStepsPrice atoms φ ε δ
      = mixStepsBound n (ttcSampInradius atoms φ ε δ) (ttcSampDiamPrice atoms φ ε δ)
          (ttcSampStep atoms φ ε δ) (ttcSampWarmPrice atoms φ ε δ)
          (ttcSampTolPrice atoms φ ε δ) := rfl

/-- **The price dominates the steps, at every cube** — the `cSample` analogue of
`Ttc.ttcVolCoins_le_ttcVolPrice` (`Exec/PriceList`).

`Ttc.ttcSampleSteps_le` (`Exec/SampleBound`) gives the per-cube closed form; §3's three
uniform bounds and `Ttc.mixStepsBound_mono` replace the three moving arguments by values
that do not depend on the cube.  Note the tolerance enters through a **lower** bound
(`Ttc.ttcSampTolPrice_le`), because `Ttc.mixStepsBound` is decreasing in it.

Two hypotheses are **not** discharged here and are carried openly: `hMw`, that the
warm-start ratio is at least one, and `heps1`, that the tolerance is at most one.  Both
are already binders of `Ttc.ttcSampleSteps_le`. -/
theorem ttcSampleSteps_le_ttcSampStepsPrice (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) {i : Cube A}
    (hi : i ∈ toDNFd (ttcInput atoms φ))
    (hγ : 0 < ttcSampInradius atoms φ ε δ)
    (hDm : 0 < ttcSampDiam atoms φ ε δ ⟨i, hi⟩)
    (hMw : 1 ≤ ttcSampWarm atoms φ ε δ ⟨i, hi⟩)
    (heps1 : ttcSampTol atoms φ ε δ ⟨i, hi⟩ ≤ 1) :
    (ttcSampleSteps atoms φ ε δ i : ℝ) ≤ ttcSampStepsPrice atoms φ ε δ := by
  have hdl : 0 < ttcSampStep atoms φ ε δ :=
    ttcSampStep_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  have htolL : ttcSampTolPrice atoms φ ε δ ≤ ttcSampTol atoms φ ε δ ⟨i, hi⟩ :=
    ttcSampTolPrice_le atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩
  have htolpos : 0 < ttcSampTolPrice atoms φ ε δ :=
    ttcSampTolPrice_pos atoms φ ε δ hε0 hε1 hn hφ hpos
  refine le_trans (ttcSampleSteps_le atoms φ ε δ hi hn hγ hDm hdl hMw
    (lt_of_lt_of_le htolpos htolL) heps1) ?_
  exact mixStepsBound_mono hγ
    (ttcSampDiam_nonneg atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩)
    (ttcSampDiam_le atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩) hMw
    (ttcSampWarm_le atoms φ ε δ hε0 hε1 hn hφ hpos ⟨i, hi⟩) htolpos htolL heps1

end AtTheRun

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.mixStepsGeom
#print axioms Ttc.mixStepsBound_eq
#print axioms Ttc.mixStepsGeom_nonneg
#print axioms Ttc.mixStepsGeom_mono_Dm
#print axioms Ttc.mixStepsLog_nonneg
#print axioms Ttc.mixStepsBound_mono_Dm
#print axioms Ttc.mixStepsBound_mono_Mw
#print axioms Ttc.mixStepsBound_anti_eps
#print axioms Ttc.mixStepsBound_mono
#print axioms Ttc.ball_subset_canon_body
#print axioms Ttc.volume_canon_body_ne_top
#print axioms Ttc.toReal_volume_canon_body_le
#print axioms Ttc.toReal_volume_canonInflated_le
#print axioms Ttc.toReal_volume_canonInflated_pos
#print axioms Ttc.canonDm_le_diam_smul_sol
#print axioms Ttc.algScale_pos
#print axioms Ttc.volSol_preprocess
#print axioms Ttc.volSol_algAtoms
#print axioms Ttc.ttcSampKappa
#print axioms Ttc.ttcSampInradius_eq
#print axioms Ttc.ttcSampInradius_model
#print axioms Ttc.ttcSampStep_eq
#print axioms Ttc.ttcSampKappa_nonneg
#print axioms Ttc.ttcSampStep_pos
#print axioms Ttc.one_le_ttcSampFactor
#print axioms Ttc.ttcSampVolPrice
#print axioms Ttc.ttcSampVolPrice_def
#print axioms Ttc.ttcSampVolPrice_model
#print axioms Ttc.toReal_volume_ttcSampBody_le
#print axioms Ttc.toReal_volume_ttcSampBody_pos
#print axioms Ttc.ttcSampVolPrice_pos
#print axioms Ttc.ttcSampDiamPrice
#print axioms Ttc.ttcSampDiamPrice_model
#print axioms Ttc.ttcSampDiam_le
#print axioms Ttc.ttcSampDiam_nonneg
#print axioms Ttc.ttcSampWarmPrice
#print axioms Ttc.ttcSampWarm_le
#print axioms Ttc.ttcSampTolPrice
#print axioms Ttc.ttcSampTolPrice_le
#print axioms Ttc.ttcSampTolPrice_pos
#print axioms Ttc.ttcSampStepsPrice
#print axioms Ttc.ttcSampStepsPrice_def
#print axioms Ttc.ttcSampleSteps_le_ttcSampStepsPrice
