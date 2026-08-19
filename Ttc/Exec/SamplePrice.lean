/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.SampleDischarge

/-!
# `Exec/SamplePrice`: the `cSample` half of the price list

`Exec/PriceList` is the `cVol` half: `Ttc.ttcVolPrice` is the uniform per-call price of the
constructed `Vol_ED`, and `Ttc.ttcVolCoins_le_ttcVolPrice` is the lemma that makes it a
*price* rather than a numeral — it dominates the coins the run's own volume oracle reads at
**every** cube of the DNF.  This file does the same for `cSample`, and lives in its own file
only because it consumes `Ttc.ttcSampStepsPrice` (`Exec/InflateBound`), which is *downstream*
of `Exec/PriceList`; logically the two belong side by side, and `Exec/PriceList`'s docstring
points here.

## The price

```
ttcSampPrice atoms φ ε δ = ⌈ttcSampStepsPrice atoms φ ε δ⌉₊ : ℕ
```

`Ttc.ttcSampStepsPrice` is `Ttc.mixStepsBound` at **uniform** arguments — the inflated
inradius, the ball-walk step, and `Exec/InflateBound` §3's three cube-free values
`Ttc.ttcSampDiamPrice`, `Ttc.ttcSampWarmPrice`, `Ttc.ttcSampTolPrice`.  It is real-valued;
`Ttc.ttcCost` charges a natural per sample, so the price is its `Nat.ceil`.

**Why `⌈·⌉₊` and not `⌈·⌉₊ + 1`,** which is the shape `Ttc.ttcVolPrice` has.  The `+ 1` there
comes from the *per-cube* form `Ttc.MonteCarlo.nSamp_roundBody_le`, which is itself
`⌈…⌉₊ + 1`.  `Ttc.mixStepsBound` already carries its `+ 1` — it is the `Nat.ceil` slack of
`Arlib.MarkovChains.mixingTime_le` — inside the real expression, so ceiling it once is
enough and a second `+ 1` would be slack with nothing to pay for.

## What makes it a price

`Ttc.ttcSampleSteps_le_ttcSampPrice`, the analogue of `Ttc.ttcVolCoins_le_ttcVolPrice`:

```
ttcSampleSteps atoms φ ε δ i ≤ ttcSampPrice atoms φ ε δ      for every cube i
```

under the **five conditions on the input alone** — `0 < ε`, `ε ≤ 1`, `1 ≤ n`,
`φ.IsPositive`, `0 < volSol (atomSet atoms) φ` — and no geometric side condition.  On the
DNF it is `Ttc.ttcSampleSteps_le_ttcSampStepsPrice_run` (`Exec/SampleDischarge`) pushed
through `Nat.ceil_le_ceil`; off it `Ttc.ttcSampleSteps` is `0` and there is nothing to prove.

`Ttc.ttcSampPrice_model` spells the same natural out in `Ttc/Model/` vocabulary, by `rfl`.
Every `Ttc` constant in it — `Ttc.algBlock`, `Ttc.algPrec`, `Ttc.algGamma`, `Ttc.algScale`,
`Ttc.algAtoms`, `Ttc.canonRfac`, `Ttc.latticeScale`, `Ttc.toDNFd`, `Ttc.preprocess`,
`Ttc.sol`, `Ttc.atomSet`, `Ttc.volSol`, `Ttc.Space` — is defined under `Ttc/Model/`, the
only non-`Ttc` names being Mathlib's and `Arlib.KV97.kappaOf`/`cOf`.  That is what lets
`Ttc.ttc_volume_estimate` carry the expression in its *statement* without
`#modelClosureOfType` going red, exactly as it carries `Ttc.ttcVolPrice`'s body.

## Both halves uniform

`Ttc.ttcCoinAndStepCharge_le_prices` is `Ttc.ttcCoinAndStepCharge_le_volPrice`
(`Exec/PriceList`) with the sampler half closed too:

```
charge ≤ m · (ttcVolPrice + ttcSampPrice · ⌈Thresh⌉₊),    m = |toDNFd (preprocess atoms φ)|
```

— no sum over cubes on either side.  `Exec/PriceList`'s mixed statement is kept, since it is
the weaker and more obviously true one.

## What a number here does and does not mean

Unchanged by this file, and **not** made smaller by putting a concrete numeral where a
parameter was:

* `Ttc.kv97SampD`'s **rejection rounds are unbounded and uncounted** (`Ttc/CostModel.lean`
  §4);
* the **`while` loops of `alg:ttc` lines 32–42 are uncharged** (`Runtime`);
* per-step arithmetic is free;
* `Ttc.mixSteps` **does not occur in `Ttc.ttcRun`'s definitional closure at all** — it enters
  through `Ttc.ttcRates`, the *law* the sample coins are drawn from, while `GenerateSamples`
  in the run is the read-off `Ttc.trajGen`.  So `Ttc.ttcSampPrice` prices the chain the
  sampler's law is defined by, **not steps the modelled run takes**.

A bound on an undercount is not a bound on the count, and nothing here bounds a running time.

And the price is **exponential in `n`**: `Ttc.mixStepsBound` carries
`4ⁿ·((γ+Dm)/γ)^(4n)`, i.e. `Θ(4ⁿ·(γ+Dm)^{4n}/γ^{4n})`, and `Ttc.ttcSampVolPrice` — which
enters through the warmness and the tolerance — carries a further
`(1 + κ/(10^ρ·q·γ̂))ⁿ · 10^(ρn) · qⁿ`.
-/

namespace Ttc

open MeasureTheory Metric Set

variable {A : Type*} {n : ℕ}

section AtTheRun

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The uniform per-sample price of the constructed sampler, as a natural.**
`Nat.ceil` of `Ttc.ttcSampStepsPrice` (`Exec/InflateBound` §4), which is
`Ttc.mixStepsBound` at cube-free arguments.

The name promises a semantic identity — "the price that dominates the chain steps the
sampler's law is defined by, at every cube" — and `Ttc.ttcSampleSteps_le_ttcSampPrice` is
the lemma that proves it.

No `+ 1`: `Ttc.mixStepsBound` already contains one (module docstring).

**Exponential in `n`.** -/
noncomputable def ttcSampPrice : ℕ := ⌈ttcSampStepsPrice atoms φ ε δ⌉₊

/-- **The `Ttc/Model/` copy is this price**, by `rfl`. -/
theorem sampPricePaidAt_eq : sampPricePaidAt atoms φ ε δ = ttcSampPrice atoms φ ε δ := rfl

theorem ttcSampPrice_def :
    ttcSampPrice atoms φ ε δ = ⌈ttcSampStepsPrice atoms φ ε δ⌉₊ := rfl

set_option maxHeartbeats 4000000 in
/-- **The `cSample` price, spelled out in `Ttc/Model/` vocabulary**, by `rfl` — the form
`Ttc.ttc_volume_estimate` carries in its statement.  See the module docstring for the list
of constants and why they are all inside the audit surface. -/
theorem ttcSampPrice_model :
    ttcSampPrice atoms φ ε δ =
      ⌈(Real.log ((1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))) / (latticeScale (algPrec atoms φ ε δ) *
        algGamma atoms φ ε δ)) ^ n * (latticeScale (algPrec atoms φ ε δ) ^ n *
        (algScale atoms φ ε δ ^ n * volSol (atomSet atoms) φ)) / (volume (Metric.ball
        (0 : Space n) (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ)))))).toReal) + 2 * Real.log (1 /
        ((algBlock atoms φ ε δ).epsPrime / (4 * ((1 +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))) / (latticeScale (algPrec atoms φ ε δ) *
        algGamma atoms φ ε δ)) ^ n * (latticeScale (algPrec atoms φ ε δ) ^ n *
        (algScale atoms φ ε δ ^ n * volSol (atomSet atoms) φ))))))) * (1024 *
        (((latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ)))) + ((1 +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))) / (latticeScale (algPrec atoms φ ε δ) *
        algGamma atoms φ ε δ)) * Metric.diam ((fun x : Space n =>
        latticeScale (algPrec atoms φ ε δ) • x) '' sol (atomSet (algAtoms atoms φ ε δ))
        (preprocess atoms φ)))) / (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))))) ^ (2 * n) + 16384 * 4 ^ n * (n : ℝ) ^ 2 * ((1
        + Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))) / (latticeScale (algPrec atoms φ ε δ) *
        algGamma atoms φ ε δ)) * Metric.diam ((fun x : Space n =>
        latticeScale (algPrec atoms φ ε δ) • x) '' sol (atomSet (algAtoms atoms φ ε δ))
        (preprocess atoms φ))) ^ 2 / (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)
        ^ 2 * (((latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ)))) + ((1 +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))) / (latticeScale (algPrec atoms φ ε δ) *
        algGamma atoms φ ε δ)) * Metric.diam ((fun x : Space n =>
        latticeScale (algPrec atoms φ ε δ) • x) '' sol (atomSet (algAtoms atoms φ ε δ))
        (preprocess atoms φ)))) / (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
        Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
        (canonRfac (toDNFd (preprocess atoms φ))))) ^ (4 * n)) + 1⌉₊
      := rfl

/-- **The price dominates the steps, at every cube** — the `cSample` analogue of
`Ttc.ttcVolCoins_le_ttcVolPrice` (`Exec/PriceList`), and what makes
`Ttc.ttcSampPrice` a price rather than an arbitrary natural.

`Ttc.ttcSampleSteps atoms φ ε δ i` is the number of ball-walk iterates in the law the run's
own `GenerateSamples` draw at cube `i` is defined by (`Ttc.ttcRates_eq_e2eSampD`, by `rfl`),
and it is at most `Ttc.ttcSampPrice` for **every** `i`, with no dependence on the cube left
on the right and no geometric hypothesis: the five binders are conditions on the input, the
same five the headline already carries. -/
theorem ttcSampleSteps_le_ttcSampPrice (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) (i : Cube A) :
    ttcSampleSteps atoms φ ε δ i ≤ ttcSampPrice atoms φ ε δ := by
  classical
  by_cases hi : i ∈ toDNFd (ttcInput atoms φ)
  · have h : (ttcSampleSteps atoms φ ε δ i : ℝ) ≤ ttcSampStepsPrice atoms φ ε δ :=
      ttcSampleSteps_le_ttcSampStepsPrice_run atoms φ ε δ hε0 hε1 hn hφ hpos hi
    calc ttcSampleSteps atoms φ ε δ i
        = ⌈((ttcSampleSteps atoms φ ε δ i : ℕ) : ℝ)⌉₊ := (Nat.ceil_natCast _).symm
      _ ≤ ⌈ttcSampStepsPrice atoms φ ε δ⌉₊ := Nat.ceil_le_ceil h
  · have h0 : ttcSampleSteps atoms φ ε δ i = 0 := by
      simp only [ttcSampleSteps, dif_neg hi]
    rw [h0]
    exact Nat.zero_le _

/-- **The run's charge, with *both* prices uniform and closed.**

```
charge ≤ m · (ttcVolPrice + ttcSampPrice · ⌈Thresh⌉₊),   m = |toDNFd (preprocess atoms φ)|
```

`Ttc.ttcCoinAndStepCharge_le_volPrice` (`Exec/PriceList` §3) is the same statement with the
sampler half left as a sum over cubes; it was the honest shape while no uniform bound on
`Ttc.ttcSampleSteps` existed, and it is kept because it is weaker.  This one supersedes it.

**Not a running-time bound**: the four undercounts of the module docstring stand. -/
theorem ttcCoinAndStepCharge_le_prices (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ)
    (c : ℕ → Space n) (t : ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ)
    (hterm : ttcTerminates atoms φ ε δ c t) :
    ttcCoinAndStepCharge atoms φ ε δ c t
      ≤ (toDNFd (preprocess atoms φ)).length
          * (ttcVolPrice atoms φ ε δ
              + ttcSampPrice atoms φ ε δ * ⌈ttcThresh atoms φ ε δ⌉₊) := by
  refine le_trans (ttcCoinAndStepCharge_le_sum atoms φ ε δ c t hterm) ?_
  refine le_trans (List.sum_le_sum (l := toDNFd (preprocess atoms φ))
    (f := fun i => ttcVolCoins atoms φ ε δ i
      + ttcSampleSteps atoms φ ε δ i * ⌈ttcThresh atoms φ ε δ⌉₊)
    (g := fun _ => ttcVolPrice atoms φ ε δ
      + ttcSampPrice atoms φ ε δ * ⌈ttcThresh atoms φ ε δ⌉₊) ?_) ?_
  · intro i _
    exact Nat.add_le_add
      (ttcVolCoins_le_ttcVolPrice atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 i)
      (Nat.mul_le_mul_right _
        (ttcSampleSteps_le_ttcSampPrice atoms φ ε δ hε0 hε1 hn hφ hpos i))
  · rw [List.map_const', List.sum_replicate, smul_eq_mul]

end AtTheRun

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ttcSampPrice
#print axioms Ttc.ttcSampPrice_def
#print axioms Ttc.ttcSampPrice_model
#print axioms Ttc.ttcSampleSteps_le_ttcSampPrice
#print axioms Ttc.ttcCoinAndStepCharge_le_prices
