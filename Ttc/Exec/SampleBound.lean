/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.CostModel

/-!
# `Exec/SampleBound`: the closed form for `cSample`, and it is exponential in `n`

`Ttc.mixCost_le_e2eBallWalkSteps` (`Ttc/CostModel.lean`) bounds the derived step cost of the
sampler's chain — the thing `cSample` denotes — by `Ttc.e2eBallWalkSteps`, which is
`Ttc.mixSteps` at the run's own geometry, which is

```
Ttc.mixSteps n γ Dm δ Mw eps
  = Arlib.MarkovChains.conductanceMixingTime Mw
      (min ((γ/(γ+Dm))^n / 32)                                   -- branch ①
           ((1/2)^n / Dm * ((γ/(γ+Dm))^n)^2 * δ / (128·n)))      -- branch ②
      eps
```

Until this file that was where the arithmetic stopped: `conductanceMixingTime` is a
`Nat.ceil` of a logarithm over a conductance, and no expression in `n`, `γ`, `Dm`, `δ`,
`Mw`, `eps` had been produced for it.  This file produces one.

## The closed form

`Ttc.mixStepsBound` is the expression, and `Ttc.mixSteps_le` is the proof:

```
mixSteps n γ Dm δ Mw eps
  ≤ (log Mw + 2·log (1/eps))
      · ( 1024 · ((γ+Dm)/γ)^(2n)                                 -- from branch ①
        + 16384 · 4^n · n² · Dm²/δ² · ((γ+Dm)/γ)^(4n) )          -- from branch ②
    + 1
```

for `1 ≤ n`, `0 < γ`, `0 < Dm`, `0 < δ`, `1 ≤ Mw`, `0 < eps ≤ 1`.  Every constant is
visible: the `1024` is `32²`, the `16384` is `128²`, the `4^n` is `(2^n)²`, and the `+1` is
the `Nat.ceil` slack of `Arlib.MarkovChains.mixingTime_le`.  There is no
`conductanceMixingTime`, no `mixSteps`, and no opaque term in it.

The route is `Arlib.MarkovChains.conductanceMixingTime_le`,

```
(conductanceMixingTime M phi eps : ℝ) ≤ (log M + 2·log (1/eps)) / phi² + 1,
```

composed with the conductance floor above.  Because `phi` is a **`min`**, `phi⁻²` is a
**`max`**, and the bound above is the sum of the two branches' contributions
(`Ttc.div_min_sq_le`) — neither branch is silently dropped.

## **It is exponential in `n`, and that is the point**

`((γ+Dm)/γ)^(4n)` and `4^n` are both exponential in the dimension.  Concretely the
dominant term is

```
16384 · n² · (Dm/δ)² · 4^n · ((γ+Dm)/γ)^(4n) · (log Mw + 2 log(1/eps)),
```

i.e. **`4^n · (γ+Dm)^{4n}/γ^{4n}`**, because the conductance floor carries `(γ/(γ+Dm))^n`
and `(1/2)^n` and `phi⁻²` squares both.  A reader who sees a concrete arithmetic
expression where a parameter used to be will assume a polynomial bound; this one is not.
`Ttc.ttcComplexity` remains polynomial in `m`, `ε`, `δ` *given* `cVol` and `cSample` — and
this file is the measurement of how large the `cSample` it is given actually is.

## Which branch dominates, and when

Branch ② is the smaller of the two — hence the dominant contribution to `phi⁻²` — whenever

```
1 ≤ n,  0 < γ ≤ Dm,  0 < δ ≤ γ,  0 < Dm
```

(`Ttc.branchTwo_le_branchOne`).  Those hypotheses are not a special case: a ball of radius
`γ` inside a body of diameter `Dm` forces `2γ ≤ Dm`, and the ball-walk step `δ` is at most
the inradius `γ` (it is exactly the hypothesis `hδγ` of `Ttc.mixCost_le_mixSteps`).  So in
every geometrically consistent instance branch ② wins, and `Ttc.mixSteps_le_branchTwo` gives
the sharper bound with branch ① dropped:

```
mixSteps n γ Dm δ Mw eps
  ≤ (log Mw + 2·log (1/eps)) · 16384 · 4^n · n² · Dm²/δ² · ((γ+Dm)/γ)^(4n) + 1.
```

Branch ① could only dominate if `(γ/(γ+Dm))^n · δ > 4·n·Dm·2^n`, which needs `δ > 4·Dm·2^n`
— a step longer than the body, i.e. no chain at all.  `Ttc.mixSteps_le` is stated without
that hypothesis anyway, so nothing is assumed about which branch is in force.

## At the run's own data

`Ttc.ttcSampleSteps_eq_mixSteps` (by `rfl` after `Ttc.ttcSampleSteps_eq_of_mem`) pins the
run's per-cube step count to `Ttc.mixSteps` at five named quantities read off the run:

| symbol | `Ttc` name | what the run supplies |
| --- | --- | --- |
| `γ` | `Ttc.ttcSampInradius` | `10^ρ·γ̂ + κ`, the inscribed radius of the inflated body |
| `Dm` | `Ttc.ttcSampDiam` | `(1 + κ/(10^ρ·γ̂))·Dm i`, its diameter |
| `δ` | `Ttc.ttcSampStep` | `10^ρ·γ̂`, the ball-walk step |
| `Mw` | `Ttc.ttcSampWarm` | `Vol P'ᵢ / Vol B(10^ρ·cᵢ, γ)`, the warmness of the start |
| `eps` | `Ttc.ttcSampTol` | `ε'/(4·Vol P'ᵢ)`, the TV tolerance |

and `Ttc.ttcSampleSteps_le` is the closed form at exactly those.  `Ttc.mixCost_le_ceil` and
`Ttc.mixCost_le_ceil_mixStepsBound` carry it back to `Ttc.mixCost`, the derived cost itself.

## The caveat, restated — this prices a law, not a run

`Exec/Complexity` §4 records, and this file does not change, that **`Ttc.mixSteps` does not
occur in `Ttc.ttcRun`'s definitional closure at all.**  It enters through `Ttc.ttcRates`,
the *law* the sample coins are drawn from; the run's `GenerateSamples` is `Ttc.trajGen`, a
read-off of a row of naturals.  So everything below prices **the chain the sampler's law is
defined by**, not steps the modelled run takes.  That is the difference between a cost and a
convention, and it was established by measurement (`Ttc.ttcRates_eq_e2eSampD` and
`Ttc.e2eSampD_eq_ballWalk`, both `rfl`), not by assertion.  Two further undercounts are
unchanged: `Ttc.kv97SampD`'s rejection rounds are counted nowhere (`Ttc/CostModel.lean` §4),
and `Ttc.ttcVolCoins` still contains `Ttc.MonteCarlo.rad`, a `Classical.choice` term with no
derivable upper bound — so this file closes the `cSample` half of `Exec/Complexity` §4's
open arithmetic and not the `cVol` half.

Nothing in `Ttc/Model/` is touched, and no new `axiom`, `sorry` or asserted `def` is
introduced: `Ttc.mixStepsBound` and the five `ttcSamp*` abbreviations are closed
expressions, each tied to what it names by a proved (`rfl`) lemma.
-/

namespace Ttc

open MeasureTheory

open scoped ENNReal

/-! # §1  The two arithmetic ingredients

Nothing here mentions `TTC` or a Markov chain: `Ttc.div_min_sq_le` is the `min`/`max`
bookkeeping that keeps both branches, and the two `one_div_branch*_sq` lemmas are the
reciprocals of the branches, in closed form. -/

/-- **`phi⁻²` at a `min` is bounded by the sum of the two branches' reciprocals.**

`phi = min A B` gives `phi⁻² = max A⁻² B⁻² ≤ A⁻² + B⁻²`, so no branch is dropped.  This is
the one place where the `min` of `Ttc.mixSteps`' conductance floor is handled, and it is
handled by keeping both terms rather than by choosing one. -/
theorem div_min_sq_le {L A B : ℝ} (hL : 0 ≤ L) :
    L / min A B ^ 2 ≤ L * (1 / A ^ 2 + 1 / B ^ 2) := by
  rcases le_total A B with h | h
  · rw [min_eq_left h]
    have h1 : 0 ≤ L * (1 / B ^ 2) := mul_nonneg hL (by positivity)
    have h2 : L / A ^ 2 = L * (1 / A ^ 2) := by ring
    rw [h2, mul_add]
    linarith
  · rw [min_eq_right h]
    have h1 : 0 ≤ L * (1 / A ^ 2) := mul_nonneg hL (by positivity)
    have h2 : L / B ^ 2 = L * (1 / B ^ 2) := by ring
    rw [h2, mul_add]
    linarith

/-- **The reciprocal square of branch ①**, in closed form:
`1 / ((γ/(γ+Dm))^n / 32)² = 1024 · ((γ+Dm)/γ)^(2n)`.  The `1024` is `32²`; the exponential
is `((γ+Dm)/γ)^(2n)`. -/
theorem one_div_branchOne_sq {n : ℕ} {γ Dm : ℝ} (hγ : 0 < γ) (hDm : 0 < Dm) :
    1 / ((γ / (γ + Dm)) ^ n / 32) ^ 2 = 1024 * ((γ + Dm) / γ) ^ (2 * n) := by
  have hsum : (0 : ℝ) < γ + Dm := by linarith
  have hu : (0 : ℝ) < γ / (γ + Dm) := div_pos hγ hsum
  have hun : ((γ / (γ + Dm)) ^ n) ≠ 0 := (pow_pos hu n).ne'
  have hv : (γ + Dm) / γ = (γ / (γ + Dm))⁻¹ := (inv_div γ (γ + Dm)).symm
  rw [hv, inv_pow, pow_mul']
  field_simp
  ring

/-- **The reciprocal square of branch ②**, in closed form:

```
1 / ((1/2)^n / Dm · ((γ/(γ+Dm))^n)² · δ / (128·n))²
  = 16384 · 4^n · n² · Dm²/δ² · ((γ+Dm)/γ)^(4n).
```

The `16384` is `128²`, the `4^n` is `((1/2)^n)⁻²`, and the exponential in the geometry is
`((γ+Dm)/γ)^(4n)` — the *fourth* power of `n`, because the floor already carries the square
of `(γ/(γ+Dm))^n` before `phi⁻²` squares it again. -/
theorem one_div_branchTwo_sq {n : ℕ} {γ Dm dl : ℝ} (hn : 1 ≤ n) (hγ : 0 < γ) (hDm : 0 < Dm)
    (hdl : 0 < dl) :
    1 / ((1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl / (128 * (n : ℝ))) ^ 2
      = 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2 * ((γ + Dm) / γ) ^ (4 * n) := by
  have hsum : (0 : ℝ) < γ + Dm := by linarith
  have hu : (0 : ℝ) < γ / (γ + Dm) := div_pos hγ hsum
  have hun : ((γ / (γ + Dm)) ^ n) ≠ 0 := (pow_pos hu n).ne'
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hv : (γ + Dm) / γ = (γ / (γ + Dm))⁻¹ := (inv_div γ (γ + Dm)).symm
  have h12 : ((1 : ℝ) / 2) ^ n = ((2 : ℝ) ^ n)⁻¹ := by rw [one_div, inv_pow]
  have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h2n : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rw [hv, inv_pow, pow_mul', h12, h4]
  field_simp
  ring

/-! # §2  The closed form for `Ttc.mixSteps`

`Ttc.mixStepsBound` is an ordinary real-valued expression: a logarithm, two exponentials in
`n`, and integer constants.  `Ttc.mixSteps_le` proves it is an upper bound; nothing about
it is asserted. -/

/-- **The closed-form upper bound on `Ttc.mixSteps`.**

```
(log Mw + 2·log (1/eps))
  · ( 1024 · ((γ+Dm)/γ)^(2n) + 16384 · 4^n · n² · Dm²/δ² · ((γ+Dm)/γ)^(4n) )
+ 1
```

The first summand is branch ① of `Ttc.mixSteps`' conductance floor, the second is branch ②
(`Ttc.one_div_branchOne_sq`, `Ttc.one_div_branchTwo_sq`), and the `+1` is the `Nat.ceil`
slack of `Arlib.MarkovChains.mixingTime_le`.

**Exponential in `n`**: the `4^n · ((γ+Dm)/γ)^(4n)` in the second summand is the true growth
rate, and it dominates the first summand's `((γ+Dm)/γ)^(2n)` in every geometrically
consistent regime (`Ttc.branchTwo_le_branchOne`). -/
noncomputable def mixStepsBound (n : ℕ) (γ Dm dl Mw eps : ℝ) : ℝ :=
  (Real.log Mw + 2 * Real.log (1 / eps))
      * (1024 * ((γ + Dm) / γ) ^ (2 * n)
          + 16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2 * ((γ + Dm) / γ) ^ (4 * n))
    + 1

/-- **`Ttc.mixSteps` is at most `Ttc.mixStepsBound`** — the closed form, with no
`conductanceMixingTime` and no opaque term left in it.

`Arlib.MarkovChains.conductanceMixingTime_le` supplies
`(conductanceMixingTime Mw phi eps : ℝ) ≤ (log Mw + 2 log (1/eps))/phi² + 1`; `phi` here is
the `min` of the two branches of the conductance floor, so `phi⁻²` is bounded by the *sum*
of the branches' reciprocal squares (`Ttc.div_min_sq_le`) — both are kept.

The hypotheses are the weakest the two upstream lemmas need: `1 ≤ n` (branch ② divides by
`n`), positivity of the geometry, `1 ≤ Mw` (a warmness is at least `1`), and `0 < eps ≤ 1`
(which also gives `eps ≤ √Mw`, the hypothesis `conductanceMixingTime_le` states). -/
theorem mixSteps_le {n : ℕ} {γ Dm dl Mw eps : ℝ} (hn : 1 ≤ n) (hγ : 0 < γ) (hDm : 0 < Dm)
    (hdl : 0 < dl) (hMw : 1 ≤ Mw) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    (mixSteps n γ Dm dl Mw eps : ℝ) ≤ mixStepsBound n γ Dm dl Mw eps := by
  have hsum : (0 : ℝ) < γ + Dm := by linarith
  have hu : (0 : ℝ) < γ / (γ + Dm) := div_pos hγ hsum
  have hun : (0 : ℝ) < (γ / (γ + Dm)) ^ n := pow_pos hu n
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  -- the two branches of the conductance floor
  have hA0 : (0 : ℝ) < (γ / (γ + Dm)) ^ n / 32 := by positivity
  have hB0 : (0 : ℝ) < (1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl
      / (128 * (n : ℝ)) := by
    refine div_pos (mul_pos (mul_pos (div_pos (by positivity) hDm) (pow_pos hun 2)) hdl) ?_
    linarith
  have hphi0 : (0 : ℝ) < min ((γ / (γ + Dm)) ^ n / 32)
      ((1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl / (128 * (n : ℝ))) :=
    lt_min hA0 hB0
  -- `eps ≤ 1 ≤ √Mw`
  have hsqrt : eps ≤ Real.sqrt Mw := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt Mw := Real.sqrt_le_sqrt hMw
    rw [Real.sqrt_one] at h1
    linarith
  have hL : 0 ≤ Real.log Mw + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log Mw := Real.log_nonneg hMw
    have h2 : 0 ≤ Real.log (1 / eps) := Real.log_nonneg ((one_le_div heps0).2 heps1)
    linarith
  have key := Arlib.MarkovChains.conductanceMixingTime_le hMw hphi0 heps0 hsqrt
  refine key.trans ?_
  have hmin := div_min_sq_le (L := Real.log Mw + 2 * Real.log (1 / eps))
    (A := (γ / (γ + Dm)) ^ n / 32)
    (B := (1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl / (128 * (n : ℝ))) hL
  rw [one_div_branchOne_sq hγ hDm, one_div_branchTwo_sq hn hγ hDm hdl] at hmin
  simp only [mixStepsBound]
  linarith

/-! # §3  Which branch dominates

Branch ② is the smaller of the two — so `phi = branch ②` and its reciprocal square is the
whole of `phi⁻²` — in every geometrically consistent regime.  The hypotheses below are
exactly the geometry the sampler already has: a ball of radius `γ` inside a body of diameter
`Dm` forces `γ ≤ Dm`, and `Ttc.mixCost_le_mixSteps`' hypothesis `hδγ` is `dl ≤ γ`. -/

/-- **Branch ② is at most branch ①** when `1 ≤ n`, `0 < dl ≤ γ ≤ Dm`.

Chain: `(1/2)^n ≤ 1/2` and `((γ/(γ+Dm))^n)² ≤ (γ/(γ+Dm))^n` since the base is in `(0,1]`,
and `dl/Dm ≤ γ/Dm ≤ 1`; so branch ② is at most `(γ/(γ+Dm))^n / (2·128·n) ≤
(γ/(γ+Dm))^n / 32`.  There is a factor of `8·n` of slack, which is why the conclusion needs
no more than `γ ≤ Dm`. -/
theorem branchTwo_le_branchOne {n : ℕ} {γ Dm dl : ℝ} (hn : 1 ≤ n) (hγ : 0 < γ) (hDm : 0 < Dm)
    (hdl : 0 < dl) (hdlγ : dl ≤ γ) (hγDm : γ ≤ Dm) :
    (1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl / (128 * (n : ℝ))
      ≤ (γ / (γ + Dm)) ^ n / 32 := by
  have hsum : (0 : ℝ) < γ + Dm := by linarith
  have hu0 : (0 : ℝ) < γ / (γ + Dm) := div_pos hγ hsum
  have hu1 : γ / (γ + Dm) ≤ 1 := by
    rw [div_le_one hsum]; linarith
  have hw0 : (0 : ℝ) < (γ / (γ + Dm)) ^ n := pow_pos hu0 n
  have hw1 : (γ / (γ + Dm)) ^ n ≤ 1 := pow_le_one₀ hu0.le hu1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hhalf0 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hhalf : ((1 : ℝ) / 2) ^ n ≤ 1 / 2 := by
    have h := pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hn
    simpa using h
  have hdD : dl / Dm ≤ 1 := by
    rw [div_le_one hDm]; linarith
  have hdD0 : (0 : ℝ) < dl / Dm := div_pos hdl hDm
  -- the numerator is at most `(γ/(γ+Dm))^n / 2`
  have hnum : (1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl
      ≤ (γ / (γ + Dm)) ^ n / 2 := by
    have hrw : (1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl
        = (1 / 2 : ℝ) ^ n * ((γ / (γ + Dm)) ^ n) ^ 2 * (dl / Dm) := by
      field_simp
    rw [hrw]
    calc (1 / 2 : ℝ) ^ n * ((γ / (γ + Dm)) ^ n) ^ 2 * (dl / Dm)
        ≤ (1 / 2 : ℝ) ^ n * ((γ / (γ + Dm)) ^ n) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hdD (by positivity)
      _ = (1 / 2 : ℝ) ^ n * ((γ / (γ + Dm)) ^ n) ^ 2 := by ring
      _ ≤ (1 / 2 : ℝ) * ((γ / (γ + Dm)) ^ n) ^ 2 :=
          mul_le_mul_of_nonneg_right hhalf (by positivity)
      _ ≤ (1 / 2 : ℝ) * (γ / (γ + Dm)) ^ n := by nlinarith
      _ = (γ / (γ + Dm)) ^ n / 2 := by ring
  have hden : (0 : ℝ) < 128 * (n : ℝ) := by linarith
  have hwn : (γ / (γ + Dm)) ^ n * 1 ≤ (γ / (γ + Dm)) ^ n * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnR hw0.le
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 32)]
  nlinarith [hnum, hwn, hw0]

/-- **The sharper bound, with branch ① dropped** — valid exactly when branch ② dominates,
i.e. in every geometrically consistent regime (`Ttc.branchTwo_le_branchOne`):

```
mixSteps n γ Dm δ Mw eps
  ≤ (log Mw + 2·log (1/eps)) · 16384 · 4^n · n² · Dm²/δ² · ((γ+Dm)/γ)^(4n) + 1.
```

`Ttc.mixSteps_le` does *not* assume `dl ≤ γ ≤ Dm` and keeps both branches; this one buys a
factor of roughly `((γ+Dm)/γ)^(2n)` in exchange for the geometry. -/
theorem mixSteps_le_branchTwo {n : ℕ} {γ Dm dl Mw eps : ℝ} (hn : 1 ≤ n) (hγ : 0 < γ)
    (hDm : 0 < Dm) (hdl : 0 < dl) (hdlγ : dl ≤ γ) (hγDm : γ ≤ Dm) (hMw : 1 ≤ Mw)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    (mixSteps n γ Dm dl Mw eps : ℝ)
      ≤ (Real.log Mw + 2 * Real.log (1 / eps))
          * (16384 * 4 ^ n * (n : ℝ) ^ 2 * Dm ^ 2 / dl ^ 2 * ((γ + Dm) / γ) ^ (4 * n))
        + 1 := by
  have hsum : (0 : ℝ) < γ + Dm := by linarith
  have hu : (0 : ℝ) < γ / (γ + Dm) := div_pos hγ hsum
  have hun : (0 : ℝ) < (γ / (γ + Dm)) ^ n := pow_pos hu n
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hB0 : (0 : ℝ) < (1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl
      / (128 * (n : ℝ)) := by
    refine div_pos (mul_pos (mul_pos (div_pos (by positivity) hDm) (pow_pos hun 2)) hdl) ?_
    linarith
  have hmineq : min ((γ / (γ + Dm)) ^ n / 32)
      ((1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl / (128 * (n : ℝ)))
      = (1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl / (128 * (n : ℝ)) :=
    min_eq_right (branchTwo_le_branchOne hn hγ hDm hdl hdlγ hγDm)
  have hsqrt : eps ≤ Real.sqrt Mw := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt Mw := Real.sqrt_le_sqrt hMw
    rw [Real.sqrt_one] at h1
    linarith
  have key := Arlib.MarkovChains.conductanceMixingTime_le hMw hB0 heps0 hsqrt
  have hms : (mixSteps n γ Dm dl Mw eps : ℕ)
      = Arlib.MarkovChains.conductanceMixingTime Mw
          ((1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl / (128 * (n : ℝ))) eps := by
    show Arlib.MarkovChains.conductanceMixingTime Mw _ eps = _
    rw [hmineq]
  rw [hms]
  refine key.trans ?_
  have hrw : (Real.log Mw + 2 * Real.log (1 / eps))
      / ((1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl / (128 * (n : ℝ))) ^ 2
      = (Real.log Mw + 2 * Real.log (1 / eps))
        * (1 / ((1 / 2 : ℝ) ^ n / Dm * ((γ / (γ + Dm)) ^ n) ^ 2 * dl
            / (128 * (n : ℝ))) ^ 2) := by ring
  rw [hrw, one_div_branchTwo_sq hn hγ hDm hdl]

/-! # §4  At the sampler's own geometry

`Ttc.e2eBallWalkSteps` is `Ttc.mixSteps` at the five quantities `Ttc.e2eSampD` supplies
(`Exec/Complexity` §4), so the closed form transports to it by `rfl`. -/

section E2E

variable {A : Type*} {n : ℕ}

/-- **The closed form at the sampler's own geometry.**  `Ttc.e2eBallWalkSteps` *is*
`Ttc.mixSteps` at the inflated body's inscribed radius, diameter, ball-walk step, warmness
and tolerance, so this is `Ttc.mixSteps_le` at those arguments — the proof is the
`rfl`. -/
theorem e2eBallWalkSteps_le {D : DNF A} (ρ : ℤ) (epsPrime rfac : ℝ) {Jt : Type}
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ)
    (Dm : {c : Cube A // c ∈ D} → ℝ) (i : {c : Cube A // c ∈ D}) (hn : 1 ≤ n)
    (hγ : 0 < latticeScale ρ * gammaHat
      + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
    (hDm : 0 < (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac
      / (latticeScale ρ * gammaHat)) * Dm i)
    (hdl : 0 < latticeScale ρ * gammaHat)
    (hMw : (1 : ℝ) ≤ (volume (Arlib.KV97.inflated (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rfac) /
      volume (Metric.ball (latticeScale ρ • cen i)
        (latticeScale ρ * gammaHat
          + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))).toReal)
    (heps0 : 0 < epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)).toReal))
    (heps1 : epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rfac)).toReal) ≤ 1) :
    (e2eBallWalkSteps ρ epsPrime rfac Am bv cen gammaHat Dm i : ℝ)
      ≤ mixStepsBound n
          (latticeScale ρ * gammaHat
            + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
          ((1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac
            / (latticeScale ρ * gammaHat)) * Dm i)
          (latticeScale ρ * gammaHat)
          ((volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac) /
            volume (Metric.ball (latticeScale ρ • cen i)
              (latticeScale ρ * gammaHat
                + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))).toReal)
          (epsPrime / (4 *
            (volume (Arlib.KV97.inflated (Am i) (bv i)
              (Arlib.KV97.cOf epsPrime) rfac)).toReal)) :=
  mixSteps_le hn hγ hDm hdl hMw heps0 heps1

end E2E

/-! # §5  At the run's own data

The five quantities `Ttc.ttcSampleSteps` feeds `Ttc.mixSteps`, each named and each pinned to
what it names by `Ttc.ttcSampleSteps_eq_mixSteps`, which is `rfl` after
`Ttc.ttcSampleSteps_eq_of_mem`.  These are abbreviations for sub-expressions of
`Ttc.ttcSampleSteps`' definition — no `def` here asserts anything. -/

section AtTheRun

variable {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The run's inflated dilated polytope for cube `i`** — the body the ball walk runs
in. -/
noncomputable def ttcSampBody (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) :
    Set (Space n) :=
  Arlib.KV97.inflated
    (canonAm (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ)) i)
    (canonBv (ttcAtoms atoms φ ε δ) (toDNFd (ttcInput atoms φ))
      (latticeScale (ttcPrec atoms φ ε δ)) i)
    (Arlib.KV97.cOf (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime)
    (canonRfac (toDNFd (ttcInput atoms φ)))

/-- **The run's ball-walk step** — `10^ρ · γ̂`, the dilated inscribed radius. -/
noncomputable def ttcSampStep : ℝ :=
  latticeScale (ttcPrec atoms φ ε δ) * ttcScaledRadius atoms φ ε δ

/-- **The run's inscribed radius** — `10^ρ · γ̂ + κ`, step plus Kannan–Vempala inflation. -/
noncomputable def ttcSampInradius : ℝ :=
  ttcSampStep atoms φ ε δ
    + Arlib.KV97.kappaOf
        (Arlib.KV97.cOf (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime)
        (canonRfac (toDNFd (ttcInput atoms φ)))

/-- **The run's diameter bound for cube `i`** — `(1 + κ/(10^ρ·γ̂)) · Dm i`. -/
noncomputable def ttcSampDiam (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) : ℝ :=
  (1 + Arlib.KV97.kappaOf
      (Arlib.KV97.cOf (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime)
      (canonRfac (toDNFd (ttcInput atoms φ))) / ttcSampStep atoms φ ε δ)
    * canonDm (atomSet (ttcAtoms atoms φ ε δ)) (toDNFd (ttcInput atoms φ))
        (ttcPrec atoms φ ε δ) i

/-- **The run's warm-start ratio for cube `i`** — `Vol P'ᵢ / Vol B(10^ρ·cᵢ, γ)`. -/
noncomputable def ttcSampWarm (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) : ℝ :=
  (volume (ttcSampBody atoms φ ε δ i) /
    volume (Metric.ball (latticeScale (ttcPrec atoms φ ε δ) • ttcCen atoms φ ε δ i)
      (ttcSampInradius atoms φ ε δ))).toReal

/-- **The run's TV tolerance for cube `i`** — `ε' / (4 · Vol P'ᵢ)`. -/
noncomputable def ttcSampTol (i : {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)}) : ℝ :=
  (inputParamsTotal (ttcAtoms atoms φ ε δ) (ttcInput atoms φ) ε δ).epsPrime
    / (4 * (volume (ttcSampBody atoms φ ε δ i)).toReal)

/-- **The run's per-cube step count is `Ttc.mixSteps` at the five named quantities**, by
`rfl` — so none of the five `def`s above stands in for an unproved identification. -/
theorem ttcSampleSteps_eq_mixSteps {i : Cube A} (hi : i ∈ toDNFd (ttcInput atoms φ)) :
    ttcSampleSteps atoms φ ε δ i
      = mixSteps n (ttcSampInradius atoms φ ε δ) (ttcSampDiam atoms φ ε δ ⟨i, hi⟩)
          (ttcSampStep atoms φ ε δ) (ttcSampWarm atoms φ ε δ ⟨i, hi⟩)
          (ttcSampTol atoms φ ε δ ⟨i, hi⟩) := by
  rw [ttcSampleSteps_eq_of_mem atoms φ ε δ hi]
  rfl

/-- **The closed form for `cSample` at the run's own data.**

`Ttc.ttcSampleSteps atoms φ ε δ i` — the number of lazy-ball-walk steps in the law of one
sample from cube `i` of the run — is at most

```
(log Mwᵢ + 2·log (1/epsᵢ))
  · ( 1024 · ((γ+Dmᵢ)/γ)^(2n)
    + 16384 · 4^n · n² · Dmᵢ²/δ² · ((γ+Dmᵢ)/γ)^(4n) )
+ 1
```

at `γ = Ttc.ttcSampInradius`, `Dmᵢ = Ttc.ttcSampDiam`, `δ = Ttc.ttcSampStep`,
`Mwᵢ = Ttc.ttcSampWarm`, `epsᵢ = Ttc.ttcSampTol`.  **Exponential in `n`** — see the module
docstring — and it prices the chain the sampler's *law* is defined by, not steps
`Ttc.ttcRun` takes. -/
theorem ttcSampleSteps_le {i : Cube A} (hi : i ∈ toDNFd (ttcInput atoms φ)) (hn : 1 ≤ n)
    (hγ : 0 < ttcSampInradius atoms φ ε δ)
    (hDm : 0 < ttcSampDiam atoms φ ε δ ⟨i, hi⟩)
    (hdl : 0 < ttcSampStep atoms φ ε δ)
    (hMw : 1 ≤ ttcSampWarm atoms φ ε δ ⟨i, hi⟩)
    (heps0 : 0 < ttcSampTol atoms φ ε δ ⟨i, hi⟩)
    (heps1 : ttcSampTol atoms φ ε δ ⟨i, hi⟩ ≤ 1) :
    (ttcSampleSteps atoms φ ε δ i : ℝ)
      ≤ mixStepsBound n (ttcSampInradius atoms φ ε δ) (ttcSampDiam atoms φ ε δ ⟨i, hi⟩)
          (ttcSampStep atoms φ ε δ) (ttcSampWarm atoms φ ε δ ⟨i, hi⟩)
          (ttcSampTol atoms φ ε δ ⟨i, hi⟩) := by
  rw [ttcSampleSteps_eq_mixSteps atoms φ ε δ hi]
  exact mixSteps_le hn hγ hDm hdl hMw heps0 heps1

/-- **The sharper, branch-②-only form at the run's own data**, under the geometry that
already holds for the sampler: step at most inradius at most diameter. -/
theorem ttcSampleSteps_le_branchTwo {i : Cube A} (hi : i ∈ toDNFd (ttcInput atoms φ))
    (hn : 1 ≤ n) (hγ : 0 < ttcSampInradius atoms φ ε δ)
    (hDm : 0 < ttcSampDiam atoms φ ε δ ⟨i, hi⟩)
    (hdl : 0 < ttcSampStep atoms φ ε δ)
    (hdlγ : ttcSampStep atoms φ ε δ ≤ ttcSampInradius atoms φ ε δ)
    (hγDm : ttcSampInradius atoms φ ε δ ≤ ttcSampDiam atoms φ ε δ ⟨i, hi⟩)
    (hMw : 1 ≤ ttcSampWarm atoms φ ε δ ⟨i, hi⟩)
    (heps0 : 0 < ttcSampTol atoms φ ε δ ⟨i, hi⟩)
    (heps1 : ttcSampTol atoms φ ε δ ⟨i, hi⟩ ≤ 1) :
    (ttcSampleSteps atoms φ ε δ i : ℝ)
      ≤ (Real.log (ttcSampWarm atoms φ ε δ ⟨i, hi⟩)
            + 2 * Real.log (1 / ttcSampTol atoms φ ε δ ⟨i, hi⟩))
          * (16384 * 4 ^ n * (n : ℝ) ^ 2 * ttcSampDiam atoms φ ε δ ⟨i, hi⟩ ^ 2
              / ttcSampStep atoms φ ε δ ^ 2
              * ((ttcSampInradius atoms φ ε δ + ttcSampDiam atoms φ ε δ ⟨i, hi⟩)
                  / ttcSampInradius atoms φ ε δ) ^ (4 * n))
        + 1 := by
  rw [ttcSampleSteps_eq_mixSteps atoms φ ε δ hi]
  exact mixSteps_le_branchTwo hn hγ hDm hdl hdlγ hγDm hMw heps0 heps1

end AtTheRun

/-! # §6  Back to `Ttc.mixCost`, the derived cost itself

`Ttc.mixCost_le_e2eBallWalkSteps` (`Ttc/CostModel.lean` §3) bounds the derived step cost by
`Ttc.e2eBallWalkSteps`; §4 bounds that by a real closed form.  Composing needs only that a
natural below a real is below its ceiling. -/

/-- **Transport a real bound on a budget to the derived cost.**  If budget `t` meets the
sampler's TV specification and `(t : ℝ) ≤ B`, then the derived cost is at most `⌈B⌉₊`. -/
theorem mixCost_le_ceil {n : ℕ} {K : Set (Space n)} {dl : ℝ} {mu0 pi : Measure (Space n)}
    {eps : ℝ≥0∞} {t : ℕ} {B : ℝ} (h1 : mixCost K dl mu0 pi eps ≤ (t : ℕ∞))
    (h2 : (t : ℝ) ≤ B) : mixCost K dl mu0 pi eps ≤ ((⌈B⌉₊ : ℕ) : ℕ∞) := by
  refine h1.trans ?_
  have : t ≤ ⌈B⌉₊ := by
    have := h2.trans (Nat.le_ceil B)
    exact_mod_cast this
  exact_mod_cast this

/-- **The derived step cost of the sampler's chain is at most `⌈Ttc.mixStepsBound⌉₊`** at the
run's geometry — the composition of `Ttc.mixCost_le_e2eBallWalkSteps` with
`Ttc.e2eBallWalkSteps_le`.

This is the end of the chain the file exists to close: `cSample` denotes `Ttc.mixCost`
(`Ttc/CostModel.lean` §3), and here it is bounded by an explicit arithmetic expression in
the run's own data, with the exponential in `n` visible in `Ttc.mixStepsBound`.  The caveat
of the module docstring is unchanged: this prices the chain the sampler's law is defined
by. -/
theorem mixCost_le_ceil_mixStepsBound {A : Type*} {n : ℕ} {D : DNF A} (hn : 1 ≤ n) (ρ : ℤ)
    (epsPrime rfac : ℝ) {Jt : Type}
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ)
    (Dm : {c : Cube A // c ∈ D} → ℝ) (i : {c : Cube A // c ∈ D})
    (hD : ∀ x ∈ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac,
      ∀ y ∈ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac,
      dist x y ≤ (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac /
        (latticeScale ρ * gammaHat)) * Dm i)
    (hγ : 0 < latticeScale ρ * gammaHat
      + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
    (hball : Metric.ball (latticeScale ρ • cen i)
        (latticeScale ρ * gammaHat + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
      ⊆ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)
    (hδ : 0 < latticeScale ρ * gammaHat)
    (hδγ : latticeScale ρ * gammaHat ≤ latticeScale ρ * gammaHat
      + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
    (hMw : (1 : ℝ) ≤ (volume (Arlib.KV97.inflated (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rfac) /
      volume (Metric.ball (latticeScale ρ • cen i)
        (latticeScale ρ * gammaHat
          + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))).toReal)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal
        ((volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac) /
          volume (Metric.ball (latticeScale ρ • cen i)
            (latticeScale ρ * gammaHat
              + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))).toReal))
        (Arlib.uniformOn volume (Metric.ball (latticeScale ρ • cen i)
          (latticeScale ρ * gammaHat
            + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)))
        (Arlib.uniformOn volume
          (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)))
    (heps : 0 < epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)).toReal))
    (hDmpos : 0 < (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac
      / (latticeScale ρ * gammaHat)) * Dm i)
    (heps1 : epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rfac)).toReal) ≤ 1) :
    mixCost (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)
        (latticeScale ρ * gammaHat)
        (Arlib.uniformOn volume (Metric.ball (latticeScale ρ • cen i)
          (latticeScale ρ * gammaHat
            + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)))
        (Arlib.uniformOn volume
          (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac))
        (ENNReal.ofReal (epsPrime / (4 *
          (volume (Arlib.KV97.inflated (Am i) (bv i)
            (Arlib.KV97.cOf epsPrime) rfac)).toReal)))
      ≤ ((⌈mixStepsBound n
            (latticeScale ρ * gammaHat
              + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
            ((1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac
              / (latticeScale ρ * gammaHat)) * Dm i)
            (latticeScale ρ * gammaHat)
            ((volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac) /
              volume (Metric.ball (latticeScale ρ • cen i)
                (latticeScale ρ * gammaHat
                  + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))).toReal)
            (epsPrime / (4 *
              (volume (Arlib.KV97.inflated (Am i) (bv i)
                (Arlib.KV97.cOf epsPrime) rfac)).toReal))⌉₊ : ℕ) : ℕ∞) :=
  mixCost_le_ceil
    (mixCost_le_e2eBallWalkSteps hn ρ epsPrime rfac Am bv cen gammaHat Dm i hD hγ hball hδ
      hδγ hMw hwarm heps)
    (e2eBallWalkSteps_le ρ epsPrime rfac Am bv cen gammaHat Dm i hn hγ hDmpos hδ hMw heps
      heps1)

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.div_min_sq_le
#print axioms Ttc.one_div_branchOne_sq
#print axioms Ttc.one_div_branchTwo_sq
#print axioms Ttc.mixStepsBound
#print axioms Ttc.mixSteps_le
#print axioms Ttc.branchTwo_le_branchOne
#print axioms Ttc.mixSteps_le_branchTwo
#print axioms Ttc.e2eBallWalkSteps_le
#print axioms Ttc.ttcSampBody
#print axioms Ttc.ttcSampStep
#print axioms Ttc.ttcSampInradius
#print axioms Ttc.ttcSampDiam
#print axioms Ttc.ttcSampWarm
#print axioms Ttc.ttcSampTol
#print axioms Ttc.ttcSampleSteps_eq_mixSteps
#print axioms Ttc.ttcSampleSteps_le
#print axioms Ttc.ttcSampleSteps_le_branchTwo
#print axioms Ttc.mixCost_le_ceil
#print axioms Ttc.mixCost_le_ceil_mixStepsBound
