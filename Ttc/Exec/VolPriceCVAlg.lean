/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CoolDrawPrice
import Ttc.Exec.PriceList
import Ttc.Exec.SampPriceHR
import Ttc.Audit.ClosureCheck
import Ttc.Witness.FullTwoCube

/-!
# `Exec/VolPriceCVAlg`: the Cousins–Vempala per-call volume price, at the algorithm's own data

`Ttc.ttcVolPrice` (`Ttc/Exec/PriceList.lean:258`) is the **hit-and-miss Monte Carlo** volume
price written as a function of the algorithm's own inputs `(atoms, φ, ε, δ)` alone, and it
is exponential in `n`.  This file is its **Cousins–Vempala replacement**: the same idea —
a per-call price that is a function of `(atoms, φ, ε, δ)` and of nothing else — applied to
`Ttc.CVCost.cvVolumeOpsPrice`, whose bound is polynomial.

> ## ⚠ FOUR THINGS THIS FILE IS NOT ⚠
>
> **1. `Ttc.ttc` does not execute this oracle.**  `Ttc.algOracles` (`Ttc/Model/Pseudocode.lean`)
> is a closed term built over `Ttc.mcVol`, the hit-and-miss Monte Carlo estimator; the price
> the *run* actually pays is `Ttc.ttcVolPrice`, and `Ttc.ttcVolCoins_le_ttcVolPrice` is the
> lemma that proves it.  **Nothing below bounds anything the modelled run does.**  It prices
> a *different* volume oracle — the one `Ttc/Volume/CVEstimator.lean` proves an accuracy
> statement for — evaluated at the run's own parameters, so that the two prices are
> comparable.  There is no lemma here of the form `ttcVolCoins … ≤ ttcVolPriceCVAlg …`: the
> two oracles read different coins, so such an inequality — if it happened to hold — would be
> an arithmetic accident between two unrelated counts, not a costing of the run.
>
> **2. The estimator being priced is conditional.**  `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns`
> leaves `hphase_mean` and `hphase_var` open (`Ttc/Volume/CVInstantiate.lean:66-67, 120, 125`),
> and `Ttc.CVEst.volume_accuracy_of_samples` carries `hsampler`, `hsample_sq` and `hend` as
> binders.  The sample count priced here is the count *those* theorems demand.
>
> **3. The per-draw charge `q` is conditional on `thm:iso`.**  The `q` slot below is
> `Ttc.CoolCost.coolDrawPrice`, whose justification as a mixing cost runs through
> `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`, which carries Cousins–Vempala's
> `thm:iso` (arXiv:1409.6011) as a **binder that is not proved anywhere in this repository**,
> together with the local-conductance floor `hell`/`hfloor`.  Read
> `Ttc/Exec/CoolDrawPrice.lean`'s header before quoting any number from this file.
>
> **4. THE REGIME CAVEAT — `n⁴` here is `n⁵` in the Cousins–Vempala regime.**  The bound
> `Ttc.CoolCost.cvVolumeOpsPrice_le_cool` used below is *arithmetic*: at the `q` this file
> substitutes, the inequality holds as stated.  But `q`'s **justification** as the cost of one
> draw needs the conductance floor `hfloor` of
> `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`, and at the step `δ = σ/8` that
> floor forces `R = O(σ)` (`Ttc/Exec/CoolDrawPrice.lean`, § *A regime warning about `hfloor`*).
> The Cousins–Vempala regime is `R ≍ σ√n`, where `δ = σ/8` cannot satisfy `hfloor`; there one
> is pushed back to `δ ≍ σ/√n`, the true per-draw cost is `n⁴` rather than `n³`, and **the
> price below is `n⁵`, not `n⁴`**.  The `n⁴` in `Ttc.ttcVolPriceCVAlg_le` lives in the
> `R = O(σ)` regime and must not be quoted outside it.

## The six slots, and where each comes from

`Ttc.CVCost.cvVolumeOpsPrice n L κ c p q` (`Ttc/Exec/VolumePriceCV.lean:169`) is
`q · cvVolumeSamplePrice n L κ c p`.  This file instantiates every slot at algorithm data:

| slot | value here | why |
| --- | --- | --- |
| `n` | the dimension | the ambient dimension of `atoms : A → LinAtom n` |
| `L` | `Ttc.cvAlgL` | `1 + log(1 + n·(γ⁻¹·diam)²)`, the body's radius ratio |
| `κ` | `Ttc.cvAlgKappa` | `ε'²/10`, the estimator's own variance budget |
| `c` | `1 + 2/n` | the single-sample relative second moment, at the largest value `Ttc.CVCost.cvVolumeSamplePrice_le` admits |
| `p` | `(algBlock …).deltaPrime` | the per-call failure probability the algorithm hands its oracles |
| `q` | `Ttc.CoolCost.coolDrawPrice n 1 ε' ⌈n·rfac⌉₊` | one draw from a cooled Gaussian phase |

* **`L`.**  `Arlib.GaussianCooling.coolPhases`' `L` is the logarithm of the total cooling
  factor, `σ_m²/σ_0² ≥ e^L`; for Cousins–Vempala `e^L ≈ n·R²` where `R` is the body's outer
  radius in units of its inner radius.  The algorithm's own inner radius is `Ttc.algGamma`
  and its own outer scale is `Metric.diam (sol …)` — the same two quantities
  `Ttc.ttcVolPrice` is built from — so the scale-invariant ratio is `γ⁻¹·diam`, and
  `Ttc.cvAlgL = 1 + log(1 + n·(γ⁻¹·diam)²)`.  The `1 +` inside the logarithm and the leading
  `1 +` are there so that `1 ≤ L` holds **unconditionally**
  (`Ttc.one_le_cvAlgL`), which is what `Ttc.CoolCost.cvVolumeOpsPrice_le_cool` demands.
  **No lemma here proves that the schedule at this `L` achieves the cooling the estimator
  needs**; `Ttc.cvAlgL` is a slot value, and its name asserts nothing.
* **`κ`.**  `Ttc.CVCost.cvVolumeSamplePrice_le_of_eps` carries `ε²/10 ≤ κ` as the conversion
  between the estimator's variance budget and its accuracy; `Ttc.cvAlgKappa` meets it with
  **equality** at the algorithm's own `ε' = ε/12`.  Hence the `κ⁻³` in the bound is
  `ε'⁻⁶` — the `ε⁻⁶` dependence `Ttc/Exec/VolumePriceCV.lean` records as *worse* than the
  paper's `ε⁻²`.
* **`M = 1` is an assumption, not a derivation.**  The brief's ingredient list omits the
  warmness `M`, but `Ttc.CoolCost.coolDrawPrice` needs one and **nothing in `(atoms, φ, ε, δ)`
  determines a phase warmness** — `Ttc/Exec/CoolDrawPrice.lean` § *Warmness* records that no
  declaration anywhere in `Arlib/Convexity/GaussianCooling/` relates `Arlib.IsWarm` to the
  schedule.  `M = 1` is the *design intent* of Gaussian cooling (consecutive phases
  `O(1)`-warm) and is **nowhere proved**.  Under a cold start `log M = Θ(n)` every exponent
  below goes up by one.
* **`ε_draw = ε'`.**  A **per-draw** total-variation tolerance.  There is **no union bound
  here** over the `r·m·k` draws the price counts, so `ε'` per draw is *not* an end-to-end
  sampling error of `ε'`; an end-to-end statement would need `ε'/(r·m·k)`, which is circular
  in the price and is not attempted.
* **`rfac`.**  `Ttc.canonRfac (toDNFd (preprocess atoms φ))`, the exact facet count of the
  preprocessed formula's canonical polytope — the same quantity the sampler side uses
  (`Ttc.ttcSampPrice_model`).

## What is proved

* `Ttc.ttcVolPriceCVAlg_def` — the price, unfolded, by `rfl`.
* `Ttc.ttcVolPriceCVAlg_le` — the bound `2⁴²·n⁴·(…)`, under **exactly the seven hypotheses
  the headline already carries** (`0 < ε`, `ε ≤ 1`, `1 ≤ n`, `φ.IsPositive`,
  `0 < volSol …`, `0 < δ`, `δ ≤ 1`) and no others: every hypothesis of
  `Ttc.CoolCost.cvVolumeOpsPrice_le_cool` is discharged from the algorithm's own invariants.
* `Ttc.ttcVolPriceCVAlg_pos` — the price is a positive natural, under five of those seven
  (`hδ0`, `hδ1` are not needed).  It is `> 0` and not the trivial `0` because
  `Ttc.Params.hr` gives the run at least one facet.
* `Ttc.ttcVolPriceCVAlg_model` — the same natural in `Ttc/Model/` vocabulary, by `rfl`, and
  `Ttc.cvAlgModelRhs` / `Ttc.cvAlgModelRhs_eq` with the `#closureReport` that measures it
  (§7 — including a finding about what the closure check counts).
* `Ttc.ttcVolPriceCVAlg_pos_two_cube`, `Ttc.ttcVolPriceCVAlg_le_two_cube` — non-vacuity: the
  seven hypotheses are jointly satisfiable, at the two-cube witness of
  `Ttc/Witness/FullTwoCube.lean`, at every `n ≥ 1` and every `(ε, δ) ∈ (0,1]²`, with the
  price positive there.

The `p` and `ε_draw` slots are not chosen freely: `Ttc.algOracles`
(`Ttc/Model/Pseudocode.lean:752-758`) hands its *own* volume oracle exactly
`(algBlock …).epsPrime` and `(algBlock …).deltaPrime`, so the CV oracle is priced at the
same per-call accuracy and confidence the run gives `Ttc.mcVol`.
-/

namespace Ttc

open MeasureTheory Metric Set

variable {A : Type*} {n : ℕ}

section AtTheRun

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-! ## §1  The two non-trivial slot values

Both are plain arithmetic `def`s over algorithm data.  Neither name asserts a semantic
identity: `cvAlgL` is "the value put in `Arlib.GaussianCooling.coolPhases`' `L` slot", not
"the logarithm of the cooling factor the schedule achieves", and `cvAlgKappa` is "the value
put in the `κ` slot", not "the variance the estimator realises". -/

/-- **The `L` slot, from the body's radius ratio.**

`1 + log(1 + n·(γ⁻¹·diam)²)` at `γ = Ttc.algGamma` and
`diam = Metric.diam (sol …)` — the two geometric quantities `Ttc.ttcVolPrice` is itself
built from, in the same `Ttc/Model/` spelling.  Mirrors Cousins–Vempala's `e^L ≈ n·R²`
with `R` the outer radius in units of the inner one.

The two `1 +`s make `1 ≤ cvAlgL` unconditional (`Ttc.one_le_cvAlgL`), which is
`Ttc.CoolCost.cvVolumeOpsPrice_le_cool`'s `hL`.

**Asserts nothing**: no lemma here proves the cooling schedule at this `L` reaches the
estimator's endpoint. -/
noncomputable def cvAlgL : ℝ :=
  1 + Real.log (1 + (n : ℝ)
    * ((algGamma atoms φ ε δ)⁻¹
        * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2)

theorem cvAlgL_def :
    cvAlgL atoms φ ε δ
      = 1 + Real.log (1 + (n : ℝ)
        * ((algGamma atoms φ ε δ)⁻¹
            * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2) :=
  rfl

/-- **The `κ` slot: the estimator's variance budget at the algorithm's own `ε'`.**

`ε'²/10` at `ε' = (Ttc.algBlock …).epsPrime = ε/12`, which meets
`Ttc.CVCost.cvVolumeSamplePrice_le_of_eps`' conversion hypothesis `ε²/10 ≤ κ` with
equality.  **Asserts nothing**: it is a slot value, not a realised variance. -/
noncomputable def cvAlgKappa : ℝ := (algBlock atoms φ ε δ).epsPrime ^ 2 / 10

theorem cvAlgKappa_def :
    cvAlgKappa atoms φ ε δ = (algBlock atoms φ ε δ).epsPrime ^ 2 / 10 := rfl

/-! ## §2  The price -/

/-- **THE COUSINS–VEMPALA PER-CALL VOLUME PRICE, AT THE ALGORITHM'S OWN INPUTS.**

`Ttc.CVCost.cvVolumeOpsPrice` at the six slot values of the module docstring's table.  A
plain arithmetic `def`; **its name asserts nothing** — in particular it does *not* assert
that it dominates anything the run reads, and it cannot: `Ttc.algOracles` executes
`Ttc.mcVol`, not this estimator (module docstring, item 1).  What is proved about it is
`Ttc.ttcVolPriceCVAlg_le` (the `n⁴` bound) and `Ttc.ttcVolPriceCVAlg_pos`.

`M = 1` — the warm-start assumption — is baked in and is **nowhere proved** (module
docstring). -/
noncomputable def ttcVolPriceCVAlg : ℕ :=
  CVCost.cvVolumeOpsPrice n (cvAlgL atoms φ ε δ) (cvAlgKappa atoms φ ε δ)
    (1 + 2 / (n : ℝ)) ((algBlock atoms φ ε δ).deltaPrime)
    (CoolCost.coolDrawPrice n 1 ((algBlock atoms φ ε δ).epsPrime)
      (CoolCost.coolStepOpCharge n (canonRfac (toDNFd (preprocess atoms φ)))))

theorem ttcVolPriceCVAlg_def :
    ttcVolPriceCVAlg atoms φ ε δ
      = CVCost.cvVolumeOpsPrice n (cvAlgL atoms φ ε δ) (cvAlgKappa atoms φ ε δ)
          (1 + 2 / (n : ℝ)) ((algBlock atoms φ ε δ).deltaPrime)
          (CoolCost.coolDrawPrice n 1 ((algBlock atoms φ ε δ).epsPrime)
            (CoolCost.coolStepOpCharge n (canonRfac (toDNFd (preprocess atoms φ))))) := rfl

/-! ## §3  The hypotheses of `Ttc.CoolCost.cvVolumeOpsPrice_le_cool`, discharged

That lemma takes twelve hypotheses — `hn hL hκ0 hκ1 hc1 hc hp0 hp1 hM heps0 heps1 hr`.  At
the slot values of §1–§2 **every one of them follows from the algorithm's own invariants**,
using only the seven conditions the headline `Ttc.ttc_volume_estimate` already carries.
This section is that discharge, lemma by lemma; §4 assembles them.

Four are unconditional (`hL`, `hc1`, `hc`, `hM`, `hκ0`), and the rest are read off the
parameter block. -/

/-- **`hL : 1 ≤ L`, unconditionally.**  `Real.log` of `1 + n·(…)²` is nonnegative because a
square is, so the leading `1 +` already gives `1 ≤ cvAlgL`.  No hypothesis on the input, and
in particular none on `Ttc.algGamma` — a degenerate `γ` (were it `0`, whence `γ⁻¹ = 0`)
only makes the ratio `0`. -/
theorem one_le_cvAlgL : 1 ≤ cvAlgL atoms φ ε δ := by
  have h0 : (0 : ℝ) ≤ (n : ℝ)
      * ((algGamma atoms φ ε δ)⁻¹
          * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2 := by
    positivity
  have h1 : (0 : ℝ) ≤ Real.log (1 + (n : ℝ)
      * ((algGamma atoms φ ε δ)⁻¹
          * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2) :=
    Real.log_nonneg (by linarith)
  rw [cvAlgL]
  linarith

/-- **`ε' = ε/12`** at the run's own block — `Ttc.Params.epsPrime` unfolded and
`Ttc.ttcBlock_eps` applied. -/
theorem algBlock_epsPrime_eq (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    (algBlock atoms φ ε δ).epsPrime = ε / 12 := by
  have he : (algBlock atoms φ ε δ).ε = ε := ttcBlock_eps atoms φ ε δ hε0 hε1 hn hφ hpos
  rw [Params.epsPrime, he]

/-- **`hκ0 : 0 < κ`** — from `Ttc.algBlock_epsPrime_pos`, which is itself unconditional
(`Ttc.Params.epsPrime_pos`). -/
theorem cvAlgKappa_pos : 0 < cvAlgKappa atoms φ ε δ := by
  have h := algBlock_epsPrime_pos atoms φ ε δ
  rw [cvAlgKappa]
  exact div_pos (pow_pos h 2) (by norm_num)

/-- **`hκ1 : κ ≤ 1`** — in fact `κ = ε²/1440 ≤ 1/1440`, from `ε ≤ 1`. -/
theorem cvAlgKappa_le_one (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : cvAlgKappa atoms φ ε δ ≤ 1 := by
  have he : (algBlock atoms φ ε δ).epsPrime = ε / 12 :=
    algBlock_epsPrime_eq atoms φ ε δ hε0 hε1 hn hφ hpos
  rw [cvAlgKappa, he]
  nlinarith

/-- **`hp1 : p ≤ 1/2`** — `δ' = (4δ/5)/(4m) = δ/(5m) ≤ 1/5` from `δ ≤ 1` and
`Ttc.Params.hm`.  This is the one discharge that consumes `hδ1`. -/
theorem algBlock_deltaPrime_le_half (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) (hδ1 : δ ≤ 1) :
    (algBlock atoms φ ε δ).deltaPrime ≤ 1 / 2 := by
  have hδblk : (algBlock atoms φ ε δ).δ = 4 * δ / 5 :=
    ttcBlock_delta atoms φ ε δ hε0 hε1 hn hφ hpos
  have hm : 1 ≤ (algBlock atoms φ ε δ).m := (algBlock atoms φ ε δ).hm
  have hmR : (1 : ℝ) ≤ ((algBlock atoms φ ε δ).m : ℝ) := by exact_mod_cast hm
  show (algBlock atoms φ ε δ).δ / (4 * ((algBlock atoms φ ε δ).m : ℝ)) ≤ 1 / 2
  rw [hδblk, div_le_iff₀ (by linarith)]
  linarith

/-- **`hr : 0 ≤ rfac`, and more: `1 ≤ rfac`.**  `Ttc.Params.hr` — "there is at least one
facet" — is a field of the block the algorithm computes, and `Ttc.ttcBlock_r` identifies
that field with the canonical facet count.  The strict form is what makes the price
*positive* (§5); `Ttc.CoolCost.cvVolumeOpsPrice_le_cool` only needs `0 ≤`.

The conclusion does not mention `δ`, and neither does the facet count; the block is read at
`δ = 0` purely to have a block to read `Ttc.Params.hr` off, and `Ttc.ttcBlock_r`'s
hypotheses contain no condition on `δ`. -/
theorem one_le_canonRfac_run (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    (1 : ℝ) ≤ canonRfac (toDNFd (preprocess atoms φ)) := by
  have h : (1 : ℝ) ≤ (algBlock atoms φ ε (0 : ℝ)).r := (algBlock atoms φ ε (0 : ℝ)).hr
  have he : (algBlock atoms φ ε (0 : ℝ)).r
      = (Nat.card (FacetIndex (toDNFd (preprocess atoms φ))) : ℝ) :=
    ttcBlock_r atoms φ ε (0 : ℝ) hε0 hε1 hn hφ hpos
  rw [he] at h
  rw [canonRfac]
  exact h

-- **`heps1 : ε_draw ≤ 1`.**  `Ttc.algBlock_epsPrime_le_one` is proved UNCONDITIONALLY in
-- `Ttc/Exec/SampPriceHR.lean`, from `Params.hε0`/`hε1` directly, needing none of this
-- file's input conditions.  This file used to carry a five-hypothesis copy of it; that
-- duplicate is gone, and the unconditional one is used at the call site below.

/-! ## §4  The bound — `2⁴²·n⁴·(algorithm-derived factors)`

`Ttc.CoolCost.cvVolumeOpsPrice_le_cool` (`Ttc/Exec/CoolDrawPrice.lean:492`) at the six slot
values of §2, with all twelve of its hypotheses discharged from §3.  **The binder list of
the theorem below is exactly the seven conditions `Ttc.ttc_volume_estimate` already carries**
— `0 < ε`, `ε ≤ 1`, `1 ≤ n`, `φ.IsPositive`, `0 < volSol …`, `0 < δ`, `δ ≤ 1` — and no
geometric or regime side condition is added.

That is a statement about *arithmetic*, not about mixing: see the module docstring's item 4
for why the exponent `4` is `5` in the Cousins–Vempala regime `R ≍ σ√n`, and items 1–3 for
what the number does and does not price. -/

/-- **THE `n⁴` BOUND, AT THE ALGORITHM'S OWN DATA.**

```
ttcVolPriceCVAlg atoms φ ε δ
  ≤ 2⁴² · n⁴ · ( (rfac + 1) · log(8/ε'²) · ( L⁴ · log(1/δ') / κ³ ) )
```

with, all four factors functions of `(atoms, φ, ε, δ)` alone:

* `rfac = Ttc.canonRfac (toDNFd (preprocess atoms φ))`, the facet count;
* `ε'   = (Ttc.algBlock atoms φ ε δ).epsPrime = ε/12`, so `log(8/ε'²) = log(1152/ε²)`;
* `L    = Ttc.cvAlgL atoms φ ε δ = 1 + log(1 + n·(γ⁻¹·diam)²)`;
* `δ'   = (Ttc.algBlock atoms φ ε δ).deltaPrime = δ/(5m)`;
* `κ    = Ttc.cvAlgKappa atoms φ ε δ = ε'²/10`, so `κ⁻³ = 1000·ε'⁻⁶` — the `ε⁻⁶` that
  `Ttc/Exec/VolumePriceCV.lean` records as *worse* than the paper's `ε⁻²`.

Under the seven headline hypotheses and nothing else.  **`M = 1` is baked into the price and
is nowhere proved** (module docstring), and the exponent `4` is conditional on the regime
caveat there. -/
theorem ttcVolPriceCVAlg_le (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (ttcVolPriceCVAlg atoms φ ε δ : ℝ)
      ≤ 2 ^ 42 * (n : ℝ) ^ 4
          * ((canonRfac (toDNFd (preprocess atoms φ)) + 1)
              * Real.log (8 / (algBlock atoms φ ε δ).epsPrime ^ 2)
              * (cvAlgL atoms φ ε δ ^ 4
                  * Real.log (1 / (algBlock atoms φ ε δ).deltaPrime)
                  / cvAlgKappa atoms φ ε δ ^ 3)) := by
  have hc1 : (1 : ℝ) ≤ 1 + 2 / (n : ℝ) := by
    have : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
    linarith
  have hr0 : (0 : ℝ) ≤ canonRfac (toDNFd (preprocess atoms φ)) := by
    have := one_le_canonRfac_run atoms φ ε hε0 hε1 hn hφ hpos
    linarith
  refine (CoolCost.cvVolumeOpsPrice_le_cool hn (one_le_cvAlgL atoms φ ε δ)
      (cvAlgKappa_pos atoms φ ε δ) (cvAlgKappa_le_one atoms φ ε δ hε0 hε1 hn hφ hpos)
      hc1 (le_refl _)
      (algBlock_deltaPrime_pos atoms φ ε δ hε0 hε1 hn hφ hpos hδ0)
      (algBlock_deltaPrime_le_half atoms φ ε δ hε0 hε1 hn hφ hpos hδ1)
      (le_refl (1 : ℝ)) (algBlock_epsPrime_pos atoms φ ε δ)
      (algBlock_epsPrime_le_one atoms φ ε δ) hr0).trans (le_of_eq ?_)
  have h8 : (8 : ℝ) * 1 / (algBlock atoms φ ε δ).epsPrime ^ 2
      = 8 / (algBlock atoms φ ε δ).epsPrime ^ 2 := by ring
  rw [h8]
  ring

/-! ## §5  The price is a positive natural

`Ttc.CVCost.cvVolumeOpsPrice` is a product, and a product of naturals is `0` as soon as one
factor is.  Two factors need an argument: the sample count needs `1 ≤ L` and `0 < κ`, and
the per-step charge `⌈n·rfac⌉₊` needs `1 ≤ n` **and** `0 < rfac` — at a formula with no
facets the price would be `0`.  §3's `Ttc.one_le_canonRfac_run` supplies the latter from
`Ttc.Params.hr`, so no extra hypothesis is needed. -/

/-- **The price is strictly positive**, under five of the headline's seven hypotheses
(`hδ0`/`hδ1` are not needed: the failure probability enters only through `Ttc.CVCost.cvRuns`,
which carries a `+ 1`). -/
theorem ttcVolPriceCVAlg_pos (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : 0 < ttcVolPriceCVAlg atoms φ ε δ := by
  have hw : 0 < CoolCost.coolStepOpCharge n (canonRfac (toDNFd (preprocess atoms φ))) := by
    have h1 : (1 : ℝ) ≤ canonRfac (toDNFd (preprocess atoms φ)) :=
      one_le_canonRfac_run atoms φ ε hε0 hε1 hn hφ hpos
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [CoolCost.coolStepOpCharge]
    exact Nat.ceil_pos.2 (by nlinarith)
  rw [ttcVolPriceCVAlg, CVCost.cvVolumeOpsPrice]
  exact Nat.mul_pos (CoolCost.coolDrawPrice_pos n 1 _ hw)
    (CVCost.cvVolumeSamplePrice_pos (1 + 2 / (n : ℝ)) ((algBlock atoms φ ε δ).deltaPrime)
      (one_le_cvAlgL atoms φ ε δ) (cvAlgKappa_pos atoms φ ε δ))

/-! ## §6  The same natural in `Ttc/Model/` vocabulary

`Ttc.ttcSampPrice_model` (`Ttc/Exec/SamplePrice.lean`) is the pattern: restate the price with
every `Ttc/Exec/` constant unfolded, by `rfl`, so that the expression can appear in a
*statement* — `#modelClosureOfType` (`Ttc/Audit/ClosureCheck.lean:285`) fails the build if a
constant in the capstone's type is defined outside `Ttc/Model/`, `Ttc/Probability/` or
`Ttc/Geometry/`.

The six `Ttc/Exec/` constants that must go are `Ttc.CVCost.cvVolumeOpsPrice`,
`Ttc.CVCost.cvRuns`, `Ttc.CVCost.cvSamplesPerPhase`, `Ttc.CoolCost.coolDrawPrice`,
`Ttc.CoolCost.coolDrawSteps`, `Ttc.CoolCost.coolPhi` and `Ttc.CoolCost.coolStepOpCharge`,
together with this file's own `Ttc.cvAlgL` and `Ttc.cvAlgKappa`; all nine are plain
arithmetic `def`s, so unfolding them leaves only

* `Ttc.algBlock`, `Ttc.algGamma`, `Ttc.algAtoms`, `Ttc.atomSet`, `Ttc.sol`,
  `Ttc.preprocess`, `Ttc.toDNFd`, `Ttc.Params.epsPrime`, `Ttc.Params.deltaPrime` — all
  `Ttc/Model/`;
* `Ttc.canonRfac`, `Ttc.FacetIndex` — `Ttc/Geometry/`;
* `Arlib.MarkovChains.lsThreshold` and `Arlib.GaussianCooling.coolPhases` — not `Ttc`
  constants, hence outside the check's scope entirely (`Ttc.Audit.closureAux` accumulates
  only names under `Ttc`), exactly as `Ttc.ttcSampPrice_model` leaves
  `Arlib.KV97.kappaOf`/`cOf` standing.

So the answer to "is the CV price expressible in the audit surface's vocabulary" is **yes**,
and the theorem below is the proof. -/

set_option maxHeartbeats 1000000 in
/-- **The price, in `Ttc/Model/` vocabulary**, by `rfl` — the form a capstone could carry in
its *statement*.  See the section docstring for the constant-by-constant account. -/
theorem ttcVolPriceCVAlg_model :
    ttcVolPriceCVAlg atoms φ ε δ
      = (⌈4 * Arlib.MarkovChains.lsThreshold 1 (Real.log 2 / (5120 * (n : ℝ)))
              ((algBlock atoms φ ε δ).epsPrime)⌉₊ + 1 + 2)
            * ⌈(n : ℝ) * canonRfac (toDNFd (preprocess atoms φ))⌉₊
          * ((⌈Real.log (1 / (algBlock atoms φ ε δ).deltaPrime)
                  / (2 * (4 / 5 - 1 / 2) ^ 2)⌉₊ + 1)
              * (Arlib.GaussianCooling.coolPhases n
                    (1 + Real.log (1 + (n : ℝ)
                      * ((algGamma atoms φ ε δ)⁻¹
                          * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
                              (preprocess atoms φ))) ^ 2))
                    ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10)
                  * (⌈(1 + 2 / (n : ℝ) - 1)
                        * (Arlib.GaussianCooling.coolPhases n
                            (1 + Real.log (1 + (n : ℝ)
                              * ((algGamma atoms φ ε δ)⁻¹
                                  * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
                                      (preprocess atoms φ))) ^ 2))
                            ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10) : ℕ)
                        / ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10)⌉₊ + 1))) := rfl

/-! ## §7  The model form's right-hand side, machine-checked against the audit surface

§6's claim — "every constant in that expression is inside `Ttc/Model/`, `Ttc/Probability/`
or `Ttc/Geometry/`" — is prose, and prose is not a check.  `Ttc.cvAlgModelRhs` below is that
right-hand side and nothing else, so that `#closureReport Ttc.cvAlgModelRhs` (run at the foot
of this file) walks it constant by constant.  `#modelClosureOfType Ttc.ttcVolPriceCVAlg_model`
would *not* do: that theorem's type also mentions `Ttc.ttcVolPriceCVAlg`, which lives here in
`Ttc/Exec/` — as does `Ttc.ttcSampPrice`, which is why the analogous check is not run on
`Ttc.ttcSampPrice_model` either.

## THE MEASUREMENT, AND A FINDING ABOUT THE CHECK ITSELF

The report reads **`100 Ttc constants, 5 outside Model/ and Probability/`**, and the five are

```
Ttc.cvAlgKappa._proof_1     : (9 + 1).AtLeastTwo
Ttc.cvAlgModelRhs._proof_1  : (3 + 1).AtLeastTwo
Ttc.cvAlgModelRhs._proof_2  : (5119 + 1).AtLeastTwo
Ttc.cvAlgModelRhs._proof_3  : (4 + 1).AtLeastTwo
Ttc.ttcVolPriceCVAlg._proof_1 : (1 + 1).AtLeastTwo
```

— i.e. **not vocabulary at all**, but the `Nat.AtLeastTwo` instances Lean lifts out of the
*real* numerals `10`, `4`, `5120`, `5`, `2` occurring in the expression.  `Nat.AtLeastTwo` is a
`Prop`-valued class, so its instances are proofs, and a proof appearing in a `def`'s body is
auto-lifted into an auxiliary `_proof_k` **named after, and filed in the module of, the
declaration that contains it**.  `Ttc.Audit.closureAux` accumulates every name under `Ttc`,
auxiliaries included, and `Ttc.Audit.outsideSurface` then files them wherever their parent
was declared — here, `Ttc/Exec/`.

Three consequences, and none of them is an obstruction:

* **The vocabulary is clean**: 95 of the 100 are `Ttc/Model/` or `Ttc/Geometry/` constants,
  and the five exceptions are numeral instances belonging to declarations of *this* file.
* **They move with the declaration.**  Written inline in a theorem's *type* inside
  `Ttc/Model/`, the same numerals lift to `Ttc.<that theorem>._proof_k` in
  `Ttc.Model.…`, which is inside the surface and the check passes.  So the CV price can be
  carried in the capstone's statement.
* **`Ttc.ttcVolPrice` does not hit this** because its body contains no real numeral `≥ 2` —
  only `+ 1` and the exponents `n`, `2`, which are `ℕ` literals needing no `AtLeastTwo`.  A
  reader comparing the two reports should not read the difference as a vocabulary
  difference.

The throwing form `#modelClosure` is therefore **not** run here: from a module under
`Ttc/Exec/` it cannot pass, for a reason that has nothing to do with what the expression
says. -/

/-- **The right-hand side of `Ttc.ttcVolPriceCVAlg_model`, as a `def`.**

Exists only so that `#modelClosure` can be run on it (section docstring); it is used by
`Ttc.cvAlgModelRhs_eq` and nowhere else.  Its name asserts nothing beyond the equation that
lemma proves. -/
noncomputable def cvAlgModelRhs : ℕ :=
  (⌈4 * Arlib.MarkovChains.lsThreshold 1 (Real.log 2 / (5120 * (n : ℝ)))
        ((algBlock atoms φ ε δ).epsPrime)⌉₊ + 1 + 2)
      * ⌈(n : ℝ) * canonRfac (toDNFd (preprocess atoms φ))⌉₊
    * ((⌈Real.log (1 / (algBlock atoms φ ε δ).deltaPrime)
            / (2 * (4 / 5 - 1 / 2) ^ 2)⌉₊ + 1)
        * (Arlib.GaussianCooling.coolPhases n
              (1 + Real.log (1 + (n : ℝ)
                * ((algGamma atoms φ ε δ)⁻¹
                    * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
                        (preprocess atoms φ))) ^ 2))
              ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10)
            * (⌈(1 + 2 / (n : ℝ) - 1)
                  * (Arlib.GaussianCooling.coolPhases n
                      (1 + Real.log (1 + (n : ℝ)
                        * ((algGamma atoms φ ε δ)⁻¹
                            * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
                                (preprocess atoms φ))) ^ 2))
                      ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10) : ℕ)
                  / ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10)⌉₊ + 1)))

/-- `Ttc.cvAlgModelRhs` **is** the price — the same `rfl` as `Ttc.ttcVolPriceCVAlg_model`,
so the closure check below is a check on the model form and not on a lookalike. -/
theorem cvAlgModelRhs_eq : ttcVolPriceCVAlg atoms φ ε δ = cvAlgModelRhs atoms φ ε δ := rfl

/-! ## §8  Non-vacuity

The seven hypotheses of `Ttc.ttcVolPriceCVAlg_le` are conditions on `(atoms, φ, ε, δ, n)`,
so the bound would be vacuous if no input met them.  `Ttc/Witness/FullTwoCube.lean`'s
two-cube data meets them at **every** `n ≥ 1` and **every** `(ε, δ) ∈ (0,1]²` — it is the
same witness `Ttc.ttc_volume_estimate_two_cube_full` uses — and there the price is a
*positive* natural, so neither the bound nor the positivity statement is empty. -/

/-- **Non-vacuity: the whole bundle is inhabited, and the price is positive there.**

At the two-cube witness (`Ttc.TwoCube.atomsT`, `Ttc.TwoCube.twoForm`), at every `n ≥ 1` and
every `(ε, δ) ∈ (0,1]²`: `hφ` is `Ttc.TwoCube.twoForm_isPositive` and `hpos` is
`Ttc.TwoCube.twoVolPos`, so all seven hypotheses of `Ttc.ttcVolPriceCVAlg_le` hold
simultaneously, and `0 < ttcVolPriceCVAlg …` — the price is not the trivial `0`. -/
theorem ttcVolPriceCVAlg_pos_two_cube (m : ℕ) (hm : 1 ≤ m) (a b : ℝ) (ha0 : 0 < a)
    (ha1 : a ≤ 1) (_hb0 : 0 < b) (_hb1 : b ≤ 1) :
    0 < ttcVolPriceCVAlg (TwoCube.atomsT m hm a b ha0 ha1) (TwoCube.twoForm m) a b :=
  ttcVolPriceCVAlg_pos (TwoCube.atomsT m hm a b ha0 ha1) (TwoCube.twoForm m) a b ha0 ha1 hm
    TwoCube.twoForm_isPositive (TwoCube.twoVolPos m hm a b ha0 ha1)

/-- **The bound itself, at the same witness** — so that `Ttc.ttcVolPriceCVAlg_le` is known to
have at least one instance whose hypotheses are all met. -/
theorem ttcVolPriceCVAlg_le_two_cube (m : ℕ) (hm : 1 ≤ m) (a b : ℝ) (ha0 : 0 < a)
    (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    (ttcVolPriceCVAlg (TwoCube.atomsT m hm a b ha0 ha1) (TwoCube.twoForm m) a b : ℝ)
      ≤ 2 ^ 42 * (m : ℝ) ^ 4
          * ((canonRfac (toDNFd (preprocess (TwoCube.atomsT m hm a b ha0 ha1)
                (TwoCube.twoForm m))) + 1)
              * Real.log (8 / (algBlock (TwoCube.atomsT m hm a b ha0 ha1)
                  (TwoCube.twoForm m) a b).epsPrime ^ 2)
              * (cvAlgL (TwoCube.atomsT m hm a b ha0 ha1) (TwoCube.twoForm m) a b ^ 4
                  * Real.log (1 / (algBlock (TwoCube.atomsT m hm a b ha0 ha1)
                      (TwoCube.twoForm m) a b).deltaPrime)
                  / cvAlgKappa (TwoCube.atomsT m hm a b ha0 ha1)
                      (TwoCube.twoForm m) a b ^ 3)) :=
  ttcVolPriceCVAlg_le (TwoCube.atomsT m hm a b ha0 ha1) (TwoCube.twoForm m) a b ha0 ha1 hm
    TwoCube.twoForm_isPositive (TwoCube.twoVolPos m hm a b ha0 ha1) hb0 hb1

end AtTheRun

end Ttc

/-! ## The audit measurement on the model form (§7)

Prints `100 Ttc constants, 5 outside Model/ and Probability/, forbidden hits: []`.  All five
are this file's own numeral auxiliaries — see §7's docstring; the vocabulary is clean. -/

#closureReport Ttc.cvAlgModelRhs

/-! ## Axiom profile -/

#print axioms Ttc.cvAlgL
#print axioms Ttc.cvAlgKappa
#print axioms Ttc.ttcVolPriceCVAlg
#print axioms Ttc.ttcVolPriceCVAlg_def
#print axioms Ttc.one_le_cvAlgL
#print axioms Ttc.algBlock_epsPrime_eq
#print axioms Ttc.cvAlgKappa_pos
#print axioms Ttc.cvAlgKappa_le_one
#print axioms Ttc.algBlock_deltaPrime_le_half
#print axioms Ttc.one_le_canonRfac_run
#print axioms Ttc.ttcVolPriceCVAlg_le
#print axioms Ttc.ttcVolPriceCVAlg_pos
#print axioms Ttc.ttcVolPriceCVAlg_model
#print axioms Ttc.cvAlgModelRhs
#print axioms Ttc.cvAlgModelRhs_eq
#print axioms Ttc.ttcVolPriceCVAlg_pos_two_cube
#print axioms Ttc.ttcVolPriceCVAlg_le_two_cube
