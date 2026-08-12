/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.Program
import Ttc.Exec.SampPriceHR
import Ttc.Exec.CoolDrawPrice
import Ttc.Exec.PolyComplexity

/-!
# `Exec/PricedHeadline`: the two closed prices the headline is now stated at

`Ttc/Model/Theorem.lean` used to quantify its running-time conjunct over two per-call
prices `cVol`, `cSample : ℕ`.  It no longer does: both are **fixed** at closed terms, so
that the runtime side can read `m · n⁴ · (…)` rather than `m · (cVol + cSample·(Θ+1))`.
This file is everything that change needs and that `Ttc/Model/` may not contain.

> ## ⚠ THE ORACLE MISMATCH — READ THIS BEFORE QUOTING ANY NUMBER BELOW ⚠
>
> The two numbers fixed here are the **Cousins–Vempala** volume price and the
> **hit-and-run** sampling price.  `Ttc.ttc`'s oracle bundle is `Ttc.algOracles`
> (`Ttc/Model/Pseudocode.lean`), a closed term over `Ttc.mcVol` (hit-and-miss Monte Carlo)
> whose sampling law is the **lazy ball walk**.  **The modelled run executes neither of the
> two oracles being priced**, and the prices it can be shown to pay — `Ttc.ttcVolPrice`
> (`Exec/PriceList`, justified by `Ttc.ttcVolCoins_le_ttcVolPrice`) and `Ttc.ttcSampPrice`
> (`Exec/SamplePrice`, justified by `Ttc.ttcSampleSteps_le_ttcSampPrice`) — are
> **exponential in `n`**.
>
> Charging these two numbers is legal arithmetic and nothing more: `cVol`/`cSample` are
> per-call **unit prices** in `Ttc.runCost`'s fold, the call **counts** are
> oracle-independent (`m` volume calls, `≤ Θ+1` samples each), and the parametric theorem
> `Ttc.ttc_volume_estimate_parametric` below holds at *every* pair of naturals.  Fixing
> them at these two is a **modelling choice**, not a costing of the run.  There is no
> lemma anywhere — here or elsewhere — of the form `ttcVolCoins … ≤` the volume number
> below, or `ttcSampleSteps … ≤` the sampling number below, and for the sampler there
> cannot be one (`Exec/SampPriceHR`, "What is *not* here").
>
> **Nothing here proves that `TTC` runs in `O(m·n⁴)`.**  Four further reasons, unchanged
> from `Exec/TheoremPoly`'s boxed warning: the hit-and-run step count is meaningful only
> under `Ttc.HitAndRunTheorem11Input` (assumed, inhabited nowhere); the per-draw charge is
> justified only through `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`,
> which carries `thm:iso` as an unproved binder; the warm start `M = 1` inside the volume
> price is nowhere proved; and the charged cost is an undercount (it prices at zero the
> arithmetic inside a call, the rejection rounds, and `alg:ttc`'s lines 32–42 loops).
>
> **The regime caveat.**  The `n⁴` holds where the body is temperature-scale (`R = O(σ)`).
> In the Cousins–Vempala regime `R ≍ σ√n` the conductance floor forces a smaller step, the
> per-draw cost becomes `n⁴` and the total `n⁵`;
> `Arlib.MarkovChains.exists_halfspace_max_lt` shows the obvious route to recovering the
> missing `√n` is **false**, not merely open.

## What is here

| declaration | what it is |
| --- | --- |
| `Ttc.ttc_volume_estimate_parametric` | the **old** headline, verbatim: both prices as binders |
| `Ttc.PricedHeadline.one_le_cvL` … `one_le_canonRfac` | the volume price's slot conditions |
| `Ttc.PricedHeadline.cvPrice_eq` | the volume price in `Ttc/Model/` vocabulary, by `rfl` |
| `Ttc.PricedHeadline.cvPrice_le` | `≤ 2⁴²·n⁴·(…)`, under the headline's own seven conditions |
| `Ttc.PricedHeadline.zero_le_volFac` | the `n`-free volume factor is nonnegative |
| `Ttc.PricedHeadline.all_ttc_cost_le_quartic` | the running-time conjunct collapsed to `m·n⁴·(…)`, prices still free |
| `Ttc.PricedHeadline.all_ttc_cost_le_quartic_at_run` | the headline's guard discharged at the run's own `R`/`γ`, leaving the two open binders `hMB`, `hepsn` |

`Ttc/Model/Theorem.lean`'s single theorem composes §1, §3 and §4 with the prices
fixed: `cvPrice_le` supplies its volume half, and its sampling half is a **guard** on the
running-time conjunct alone, so that the accuracy conjunct stays unconditional.

## Why the parametric form had to be copied rather than derived

`Ttc.ttc_volume_estimate_parametric` is `Ttc.ttc_volume_estimate` as it stood before this
change, under a new name and over `Ttc.ttcCharged` — the six-ary law that used to be called
`Ttc.ttc`, renamed on 2026-08-12 when `Ttc.ttc` became the four-ary
`TTC(F, ε, δ)` with both prices fixed inside it (`Model/Pseudocode`, `Ttc.ttc_def`).  That
rename is the *only* difference; the proposition is otherwise the old headline verbatim.  It
is **not** derivable from the
fixed-price form (a `∀` over two naturals is strictly stronger than one instance of it), so
its four-line proof is repeated.  Downstream consumers that need the prices free —
`Ttc/Exec/TheoremPoly.lean`, `Ttc/Witness/FullTwoCube.lean` — use this one.

## Why five short proofs are duplicated from `Exec/VolPriceCVAlg`

`Ttc.ttcVolPriceCVAlg` and its bound `Ttc.ttcVolPriceCVAlg_le` are exactly the volume-side
content this file needs, and **they cannot be imported**: `Ttc/Exec/VolPriceCVAlg.lean`
imports `Ttc.Audit.ClosureCheck` (for its `#closureReport`) and `Ttc.Witness.FullTwoCube`,
both of which import `Ttc/Model/Theorem.lean`, which now imports *this* file.  So §2–§3
below restate the five slot conditions and the bound over the *unfolded* expressions, with
`Exec/VolPriceCVAlg`'s own proofs.  Nothing is stated here that is not stated there; the
duplication is an import-graph artefact and would vanish if `Exec/VolPriceCVAlg`'s
reporting and witness sections were split into a file of their own.

**No definition is duplicated.**  §2–§3 introduce no `def`; every statement is written over
the arithmetic itself, which is why the expressions are spelled out.
-/

namespace Ttc

open MeasureTheory Metric Set
open Ttc.Monadic

variable {A : Type*} {n : ℕ}

/-! ## §1 — the parametric headline, preserved

`Ttc.ttc_volume_estimate` as it read before the prices were fixed.  Both conjuncts speak
about the same run, drawn from `Ttc.ttcCharged atoms φ ε δ cVol cSample`, and both prices are
binders, so the statement holds at *every* pair of naturals. -/

/-- **`thm:volumettc` + `thm:runtime`, with the two per-call prices left free.**

This is the form `Ttc.ttc_volume_estimate` had before `Ttc/Model/Theorem.lean` fixed the
prices, kept verbatim because it is the repo's **unconditional** result and because the
fixed-price form does not imply it.

* **Accuracy.** `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, at the user's own `Vol(F)`.
* **Running time.** `All[…]` is `∀ᵐ`, with no termination hypothesis: the absorption loops
  halt `Ttc.ttc`-almost surely.  The charged cost is at most `m·(cVol + cSample·(Θ+1))`.

Correctness, not efficiency: `cVol`/`cSample` are unit prices of the cost model, and the
two *constructed* oracles the accuracy half is proved for — `Ttc.mcVol` and the lazy ball
walk — are exponential in `n`. -/
theorem ttc_volume_estimate_parametric {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (cVol cSample : ℕ) :
    -- (accuracy) the estimate is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[r ← ttcCharged atoms φ ε δ cVol cSample;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) almost every run is charged at most `m·(cVol + cSample·(Θ + 1))`
    (All[r ← ttcCharged atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ)
          * ((cVol : ℝ) + (cSample : ℝ)
              * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                  + 15 * (Real.log (15 / (2 * δ))
                      + Real.log ((toDNFd (preprocess atoms φ)).length))
                  + 1))]) := by
  rw [ttcCharged_eq_ttcPairLaw]
  refine ⟨ttc_accuracy_pairLaw atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 cVol cSample, ?_⟩
  have h := all_ttcPairLaw_cost_le atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 cVol cSample
  simpa only [ttcComplexity_def] using h

namespace PricedHeadline

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-! ## §2 — the volume price's six slot conditions

`Ttc.CoolCost.cvVolumeOpsPrice_le_cool` takes twelve hypotheses.  Four are unconditional at
the slot values used here (`hc1`, `hc`, `hM`, `hκ0`) and the rest are read off the run's own
parameter block.  These are `Exec/VolPriceCVAlg` §3's lemmas restated over the unfolded
expressions — see the module docstring for why they cannot simply be imported. -/

/-- **`hL : 1 ≤ L`, unconditionally.**  `Real.log` of `1 + n·(…)²` is nonnegative because a
square is, so the leading `1 +` already gives it.  No hypothesis on `Ttc.algGamma`: a
degenerate `γ` (whence `γ⁻¹ = 0`) only makes the ratio `0`. -/
theorem one_le_cvL :
    (1 : ℝ) ≤ 1 + Real.log (1 + (n : ℝ)
      * ((algGamma atoms φ ε δ)⁻¹
          * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2) := by
  have h0 : (0 : ℝ) ≤ (n : ℝ)
      * ((algGamma atoms φ ε δ)⁻¹
          * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2 := by
    positivity
  have h1 : (0 : ℝ) ≤ Real.log (1 + (n : ℝ)
      * ((algGamma atoms φ ε δ)⁻¹
          * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2) :=
    Real.log_nonneg (by linarith)
  linarith

/-- **`hκ0 : 0 < κ`** — from `Ttc.algBlock_epsPrime_pos`, which is unconditional. -/
theorem cvKappa_pos : 0 < (algBlock atoms φ ε δ).epsPrime ^ 2 / 10 :=
  div_pos (pow_pos (algBlock_epsPrime_pos atoms φ ε δ) 2) (by norm_num)

/-- **`hκ1 : κ ≤ 1`** — in fact `κ ≤ 1/10`, from the unconditional `0 < ε' ≤ 1`
(`Ttc.algBlock_epsPrime_pos`, `Ttc.algBlock_epsPrime_le_one`). -/
theorem cvKappa_le_one : (algBlock atoms φ ε δ).epsPrime ^ 2 / 10 ≤ 1 := by
  have h0 := algBlock_epsPrime_pos atoms φ ε δ
  have h1 := algBlock_epsPrime_le_one atoms φ ε δ
  nlinarith

/-- **`hp1 : p ≤ 1/2`** — `δ' = (4δ/5)/(4m) = δ/(5m) ≤ 1/5` from `δ ≤ 1` and
`Ttc.Params.hm`.  This is the one discharge that consumes `hδ1`. -/
theorem deltaPrime_le_half (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ) (hδ1 : δ ≤ 1) :
    (algBlock atoms φ ε δ).deltaPrime ≤ 1 / 2 := by
  have hδblk : (algBlock atoms φ ε δ).δ = 4 * δ / 5 :=
    ttcBlock_delta atoms φ ε δ hε0 hε1 hn hφ hpos
  have hm : 1 ≤ (algBlock atoms φ ε δ).m := (algBlock atoms φ ε δ).hm
  have hmR : (1 : ℝ) ≤ ((algBlock atoms φ ε δ).m : ℝ) := by exact_mod_cast hm
  show (algBlock atoms φ ε δ).δ / (4 * ((algBlock atoms φ ε δ).m : ℝ)) ≤ 1 / 2
  rw [hδblk, div_le_iff₀ (by linarith)]
  linarith

/-- **`1 ≤ rfac`** — `Ttc.Params.hr` ("there is at least one facet") is a field of the block
the algorithm computes, and `Ttc.ttcBlock_r` identifies that field with the canonical facet
count.  The conclusion does not mention `δ`, and neither does the facet count; the block is
read at `δ = 0` purely to have a block to read `Ttc.Params.hr` off. -/
theorem one_le_canonRfac (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    (1 : ℝ) ≤ canonRfac (toDNFd (preprocess atoms φ)) := by
  have h : (1 : ℝ) ≤ (algBlock atoms φ ε (0 : ℝ)).r := (algBlock atoms φ ε (0 : ℝ)).hr
  have he : (algBlock atoms φ ε (0 : ℝ)).r
      = (Nat.card (FacetIndex (toDNFd (preprocess atoms φ))) : ℝ) :=
    ttcBlock_r atoms φ ε (0 : ℝ) hε0 hε1 hn hφ hpos
  rw [he] at h
  rw [canonRfac]
  exact h

/-! ## §3 — the volume price, and its `n⁴` bound

`Ttc.PricedHeadline.cvPrice_eq` is the `rfl` that turns the fully unfolded expression the
headline carries in its *statement* into `Ttc.CVCost.cvVolumeOpsPrice` at the six slot
values of `Exec/VolPriceCVAlg`'s table (`n`, `L = 1 + log(1 + n·(γ⁻¹·diam)²)`, `κ = ε'²/10`,
`c = 1 + 2/n`, `p = δ'`, `q = ` one draw from a cooled Gaussian phase at warmness `M = 1`).
It is the same number as `Ttc.ttcVolPriceCVAlg`, by the same `rfl` as
`Ttc.cvAlgModelRhs_eq`; that file is downstream and cannot be cited here. -/

set_option maxHeartbeats 1000000 in
/-- **The unfolded volume price is `Ttc.CVCost.cvVolumeOpsPrice` at the six slot values**,
by `rfl`.  The left-hand side is what `Ttc.ttc_volume_estimate` carries in its type: every
`Ttc` constant in it is defined under `Ttc/Model/` or `Ttc/Geometry/`, which is what
`#modelClosureOfType` demands. -/
theorem cvPrice_eq :
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
      = CVCost.cvVolumeOpsPrice n
          (1 + Real.log (1 + (n : ℝ)
            * ((algGamma atoms φ ε δ)⁻¹
                * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
                    (preprocess atoms φ))) ^ 2))
          ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10)
          (1 + 2 / (n : ℝ)) ((algBlock atoms φ ε δ).deltaPrime)
          (CoolCost.coolDrawPrice n 1 ((algBlock atoms φ ε δ).epsPrime)
            (CoolCost.coolStepOpCharge n (canonRfac (toDNFd (preprocess atoms φ))))) := rfl

/-- **The `n`-free volume factor of the bound is nonnegative.**

`volFac = (rfac + 1)·log(8/ε'²)·(L⁴·log(1/δ')/κ³)`: the facet count is `≥ 1`, `ε' ≤ 1` makes
`8/ε'² ≥ 8`, `δ' ≤ 1/2` makes `1/δ' ≥ 2`, and `L ≥ 1`, `κ > 0`. -/
theorem zero_le_volFac (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (0 : ℝ) ≤ (canonRfac (toDNFd (preprocess atoms φ)) + 1)
        * Real.log (8 / (algBlock atoms φ ε δ).epsPrime ^ 2)
        * ((1 + Real.log (1 + (n : ℝ)
              * ((algGamma atoms φ ε δ)⁻¹
                  * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
                      (preprocess atoms φ))) ^ 2)) ^ 4
            * Real.log (1 / (algBlock atoms φ ε δ).deltaPrime)
            / ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10) ^ 3) := by
  have hr := one_le_canonRfac atoms φ ε hε0 hε1 hn hφ hpos
  have hep0 := algBlock_epsPrime_pos atoms φ ε δ
  have hep1 := algBlock_epsPrime_le_one atoms φ ε δ
  have hL := one_le_cvL atoms φ ε δ
  have hκ0 := cvKappa_pos atoms φ ε δ
  have h8 : (1 : ℝ) ≤ 8 / (algBlock atoms φ ε δ).epsPrime ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hlog8 : (0 : ℝ) ≤ Real.log (8 / (algBlock atoms φ ε δ).epsPrime ^ 2) :=
    Real.log_nonneg h8
  have hdh := deltaPrime_le_half atoms φ ε δ hε0 hε1 hn hφ hpos hδ1
  have hdp : 0 < (algBlock atoms φ ε δ).deltaPrime :=
    algBlock_deltaPrime_pos atoms φ ε δ hε0 hε1 hn hφ hpos hδ0
  have h1d : (1 : ℝ) ≤ 1 / (algBlock atoms φ ε δ).deltaPrime := by
    rw [le_div_iff₀ hdp]; linarith
  have hlogd : (0 : ℝ) ≤ Real.log (1 / (algBlock atoms φ ε δ).deltaPrime) :=
    Real.log_nonneg h1d
  have hL0 : (0 : ℝ) ≤ (1 + Real.log (1 + (n : ℝ)
      * ((algGamma atoms φ ε δ)⁻¹
          * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
              (preprocess atoms φ))) ^ 2)) ^ 4 := by positivity
  have hquot : (0 : ℝ) ≤ (1 + Real.log (1 + (n : ℝ)
        * ((algGamma atoms φ ε δ)⁻¹
            * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
                (preprocess atoms φ))) ^ 2)) ^ 4
      * Real.log (1 / (algBlock atoms φ ε δ).deltaPrime)
      / ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10) ^ 3 :=
    div_nonneg (mul_nonneg hL0 hlogd) (by positivity)
  have hfront : (0 : ℝ) ≤ (canonRfac (toDNFd (preprocess atoms φ)) + 1)
      * Real.log (8 / (algBlock atoms φ ε δ).epsPrime ^ 2) :=
    mul_nonneg (by linarith) hlog8
  exact mul_nonneg hfront hquot

set_option maxHeartbeats 1000000 in
/-- **THE `n⁴` BOUND ON THE FIXED VOLUME PRICE**, under exactly the seven conditions the
headline already carries.

```
volume price ≤ 2⁴² · n⁴ · ( (rfac + 1) · log(8/ε'²) · ( L⁴ · log(1/δ') / κ³ ) )
```

`Ttc.CoolCost.cvVolumeOpsPrice_le_cool` at §2's discharges, with the warm start `M = 1`.
This is `Ttc.ttcVolPriceCVAlg_le` restated over the unfolded price; ⚠ `M = 1` is **nowhere
proved**, and the exponent `4` carries the module docstring's regime caveat. -/
theorem cvPrice_le (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (((⌈4 * Arlib.MarkovChains.lsThreshold 1 (Real.log 2 / (5120 * (n : ℝ)))
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
                      / ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10)⌉₊ + 1))) : ℕ) : ℝ)
      ≤ 2 ^ 42 * (n : ℝ) ^ 4
          * ((canonRfac (toDNFd (preprocess atoms φ)) + 1)
              * Real.log (8 / (algBlock atoms φ ε δ).epsPrime ^ 2)
              * ((1 + Real.log (1 + (n : ℝ)
                    * ((algGamma atoms φ ε δ)⁻¹
                        * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
                            (preprocess atoms φ))) ^ 2)) ^ 4
                  * Real.log (1 / (algBlock atoms φ ε δ).deltaPrime)
                  / ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10) ^ 3)) := by
  rw [cvPrice_eq]
  have hc1 : (1 : ℝ) ≤ 1 + 2 / (n : ℝ) := by
    have : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
    linarith
  have hr0 : (0 : ℝ) ≤ canonRfac (toDNFd (preprocess atoms φ)) := by
    have := one_le_canonRfac atoms φ ε hε0 hε1 hn hφ hpos
    linarith
  refine (CoolCost.cvVolumeOpsPrice_le_cool hn (one_le_cvL atoms φ ε δ)
      (cvKappa_pos atoms φ ε δ) (cvKappa_le_one atoms φ ε δ) hc1 (le_refl _)
      (algBlock_deltaPrime_pos atoms φ ε δ hε0 hε1 hn hφ hpos hδ0)
      (deltaPrime_le_half atoms φ ε δ hε0 hε1 hn hφ hpos hδ1)
      (le_refl (1 : ℝ)) (algBlock_epsPrime_pos atoms φ ε δ)
      (algBlock_epsPrime_le_one atoms φ ε δ) hr0).trans (le_of_eq ?_)
  have h8 : (8 : ℝ) * 1 / (algBlock atoms φ ε δ).epsPrime ^ 2
      = 8 / (algBlock atoms φ ε δ).epsPrime ^ 2 := by ring
  rw [h8]
  ring

/-! ## §4 — the running-time conjunct, collapsed to `m · n⁴ · (…)`

`Ttc.PolyComplexity.ttcComplexity_le_poly` at `K = kv = 4`, composed with
`Ttc.ttc_volume_estimate_parametric`'s running-time half.  The prices are still binders
*here*; `Ttc/Model/Theorem.lean` is where they are fixed, and this is the lemma its proof
applies.  Written with the threshold factor spelled out rather than as
`Ttc.PolyComplexity.threshFactor`, because that constant lives outside the audit surface and
the headline's type may not name it. -/

/-- **`cost ≤ m · n⁴ · (Cv·volFac + 2⁶²·rfac·(R²/γ²)·log(2R)·(Θ+1))`, almost surely.**

`Ttc.ttc_volume_estimate_parametric`'s second conjunct with both prices discharged at
quartic bounds.  No termination hypothesis: the absorption loops halt `Ttc.ttc`-almost
surely.  ⚠ A bound on the **charged** cost — one unit per oracle call, and nothing for the
arithmetic inside a call, the rejection rounds, or `alg:ttc`'s lines 32–42 loops. -/
theorem all_ttc_cost_le_quartic {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (cVol cSample : ℕ) (Cv volFac rfac R γ : ℝ)
    (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac) (hrfac : 1 ≤ rfac) (hR1 : 1 ≤ R) (hγ0 : 0 < γ)
    (hcVol : (cVol : ℝ) ≤ Cv * (n : ℝ) ^ 4 * volFac)
    (hcSample : (cSample : ℝ)
      ≤ 2 ^ 62 * (n : ℝ) ^ 4 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)) :
    All[r ← ttcCharged atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
          * (Cv * volFac
              + 2 ^ 62 * rfac * (R ^ 2 / γ ^ 2) * Real.log (2 * R)
                  * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                      + 15 * (Real.log (15 / (2 * δ))
                          + Real.log ((toDNFd (preprocess atoms φ)).length))
                      + 1))] := by
  have hrun := (ttc_volume_estimate_parametric atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
    cVol cSample).2
  have hb := PolyComplexity.ttcComplexity_le_poly atoms φ ε δ cVol cSample 4 4 hn le_rfl
    le_rfl hCv hvolFac hrfac hR1 hγ0 hε0 hε1 hδ0 hδ1 hcVol hcSample
  filter_upwards [hrun] with r hr
  exact hr.trans hb

/-! ## §5 — the headline's guard, discharged at the run's own geometry

`Ttc/Model/Theorem.lean`'s running-time conjunct is guarded by `∀ R γ, 1 ≤ R → 0 < γ →
(the fixed sampling price is `≤ 2⁶²·n⁴·rfac·(R²/γ²)·log(2R)`) → …`.  Prose is not a check,
so the lemma below *discharges* that guard at `R = Ttc.ttcSampDiamPrice`,
`γ = Ttc.ttcSampInradius`, leaving exactly the two binders the development does not prove.
-/

/-- **The guard is met at the run's own geometry, under exactly two open hypotheses.**

`Ttc.ttcSampPriceHR_le_quartic` at `R = Ttc.ttcSampDiamPrice`, `γ = Ttc.ttcSampInradius`,
`rfac = Ttc.canonRfac (toDNFd (preprocess atoms φ))`, composed with §4.  Seven of that
theorem's ten hypotheses are discharged from the headline's own binders; the two that
remain are visible here and are **not theorems of this repository**:

* `hMB : M ≤ (2R)ⁿ`, the warm start — `Exec/SamplerCost` calls it "a genuine open
  hypothesis" and nothing anywhere constructs one;
* `hepsn : 2⁻ⁿ ≤ ε'`, `cor:linf`'s own regime, a condition on the input pair `(ε, n)`.

⚠ And the number being bounded is still the **hit-and-run** price, of an oracle
`Ttc.ttc` does not call — module docstring. -/
theorem all_ttc_cost_le_quartic_at_run {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive) (hpos : 0 < volSol (atomSet atoms) φ)
    (cVol : ℕ) (Cv volFac : ℝ) (hCv : 0 ≤ Cv) (hvolFac : 0 ≤ volFac)
    (hcVol : (cVol : ℝ) ≤ Cv * (n : ℝ) ^ 4 * volFac)
    (hMB : ttcSampWarmPrice atoms φ ε δ ≤ (2 * ttcSampDiamPrice atoms φ ε δ) ^ n)
    (hepsn : 1 / 2 ^ n ≤ (algBlock atoms φ ε δ).epsPrime) :
    All[r ← ttcCharged atoms φ ε δ cVol (ttcSampPriceHR atoms φ ε δ);
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
          * (Cv * volFac
              + 2 ^ 62 * canonRfac (toDNFd (preprocess atoms φ))
                  * (ttcSampDiamPrice atoms φ ε δ ^ 2 / ttcSampInradius atoms φ ε δ ^ 2)
                  * Real.log (2 * ttcSampDiamPrice atoms φ ε δ)
                  * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                      + 15 * (Real.log (15 / (2 * δ))
                          + Real.log ((toDNFd (preprocess atoms φ)).length))
                      + 1))] :=
  all_ttc_cost_le_quartic atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos cVol
    (ttcSampPriceHR atoms φ ε δ) Cv volFac (canonRfac (toDNFd (preprocess atoms φ)))
    (ttcSampDiamPrice atoms φ ε δ) (ttcSampInradius atoms φ ε δ) hCv hvolFac
    (one_le_canonRfac atoms φ ε hε0 hε1 hn hφ hpos)
    (one_le_ttcSampDiamPrice atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcSampInradius_pos atoms φ ε δ hε0 hε1 hn hφ hpos) hcVol
    (ttcSampPriceHR_le_quartic atoms φ ε δ hε0 hε1 hn hφ hpos
      (one_le_canonRfac atoms φ ε hε0 hε1 hn hφ hpos) hMB hepsn)

end PricedHeadline

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ttc_volume_estimate_parametric
#print axioms Ttc.PricedHeadline.one_le_cvL
#print axioms Ttc.PricedHeadline.cvKappa_pos
#print axioms Ttc.PricedHeadline.cvKappa_le_one
#print axioms Ttc.PricedHeadline.deltaPrime_le_half
#print axioms Ttc.PricedHeadline.one_le_canonRfac
#print axioms Ttc.PricedHeadline.cvPrice_eq
#print axioms Ttc.PricedHeadline.zero_le_volFac
#print axioms Ttc.PricedHeadline.cvPrice_le
#print axioms Ttc.PricedHeadline.all_ttc_cost_le_quartic
#print axioms Ttc.PricedHeadline.all_ttc_cost_le_quartic_at_run
