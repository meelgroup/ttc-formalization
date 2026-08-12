/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Program
import Ttc.Prices.Fixed
import Ttc.Exec.PricedHeadline

/-!
# The main theorem: `thm:volumettc` + `thm:runtime` for `TTC(F, ε, δ)`

The **statement layer**: one theorem, `Ttc.ttc_volume_estimate`, and nothing else — no
definition, no auxiliary lemma, no proof to work through.  The accuracy half comes from
`Ttc.ttc_volume_estimate_parametric` and the running-time half from
`Ttc.PricedHeadline.all_ttc_cost_le_quartic`, both in `Ttc/Exec/PricedHeadline.lean`.

Both conjuncts speak about **the same run**, drawn from the one measure

    ttc atoms φ ε δ (cvVolPriceAt atoms φ ε δ) (hrSampPriceAt atoms φ ε δ)
      : Measure (ℝ × ℕ)

whose `Ttc.ttc` is defined in `Model/Pseudocode` and whose two per-call prices are the two
`def`s of `Ttc/Prices/Fixed.lean`: accuracy about `r.1`, running time about `r.2`.  This
mirrors `ApproxNFA.countNFAM A n ε δ : PMF (ℝ × ℕ)`.

Nine binders — `atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos`.  Among them there is no
interpretation, no parameter block, no converter, no oracle, no precision, no
inscribed-ball data and no boundedness hypothesis.

`Pr[p ← μ; E p]` is `(μ {p | E p}).toReal` and `All[p ← μ; E p]` is `∀ᵐ p ∂μ`, both from
`Monadic/MeasurePr`.

Audit path: `Model/`'s four files, `Ttc/Probability/`'s four, `Ttc/Geometry/` and
`Ttc/Prices/`.  `#modelClosureOfType Ttc.ttc_volume_estimate` (`Audit/ClosureCheck`) fails
the build if any constant in this theorem's *type* is defined outside them.  `Ttc/Prices/`
is the newest and least free of the four; the argument for admitting it, and the bound on
what may go there, are in that file's section docstring.

## ⚠ The two prices are fixed — and they are not the run's own prices ⚠

`Ttc.ttc` executes neither oracle being priced: its bundle `Ttc.algOracles` is a closed
term over `Ttc.mcVol` — hit-and-miss Monte Carlo — whose sampling law is the lazy ball
walk.  `cVol`/`cSample` are unit multipliers in `Ttc.stepCost`, so substituting *any* pair
of naturals yields a bound of the shape below; at `0` it yields `r.2 ≤ 0`.  Charging
`Ttc.cvVolPriceAt` and `Ttc.hrSampPriceAt` is a **modelling choice, not a costing of this
run**.  The prices the run *can* be shown to pay are `Ttc.ttcVolPrice` (`Exec/PriceList`)
and `Ttc.ttcSampPrice` (`Exec/SamplePrice`), and both are exponential in `n`.  Read the
boxed warning at the head of `Ttc/Exec/PricedHeadline.lean` before quoting the running-time
conjunct, and **note that nothing anywhere proves `TTC` runs in `O(m·n⁴)`**: the
hit-and-run step count is meaningful only under `Ttc.HitAndRunTheorem11Input` (inhabited
nowhere), the per-draw charge rests on `thm:iso`, the charged cost is an undercount, and the
`n⁴` holds only in the temperature-scale regime `R = O(σ)` (`n⁵` at `R ≍ σ√n`, and
`Arlib.MarkovChains.exists_halfspace_max_lt` shows the obvious repair is **false**).

**The price-parametric, unconditional form has not been lost.**  It is
`Ttc.ttc_volume_estimate_parametric`, kept character for character, and it — not this
theorem — is what `Ttc/Exec/TheoremPoly.lean` and `Ttc/Witness/FullTwoCube.lean` consume.
Non-vacuity for *this* theorem is `Ttc.TwoCube.ttc_volume_estimate_two_cube_fixed`
(`Ttc/Witness/FixedPriceTwoCube.lean`).

[`AUDIT.md`](../../AUDIT.md) §1e is written to be read alongside this file, and carries
what is deliberately not restated here: which quantifier the running-time half uses and
why the pointwise form is false; why this is a `Measure` and not a `PMF`; the definitional
closure; the three preprocessing steps the headline certifies `alg:ttc` *plus*; the two
residual hypotheses `hφ` and `hpos`; and that `hbdd` was derived rather than dropped
(§1h).
-/

namespace Ttc

open MeasureTheory Set
open Ttc.Monadic

/-- **`thm:volumettc` + `thm:runtime`, at two fixed per-call prices.**  `TTC` is run on
`F = (atoms, φ)` at accuracy `ε` and confidence `δ`; both halves speak about the same run.

* **Accuracy.** `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, at the **user's own**
  `Vol(F)`, **unconditionally** under the nine binders.  The output is
  `Model/Pseudocode`'s `Ttc.ttcRun`, which takes no oracle argument.
* **Running time.** `All[…]` is `∀ᵐ`, with **no termination hypothesis**: the absorption
  loops halt `Ttc.ttc`-almost surely.  At any `(R, γ)` bounding the fixed sampling price
  quartically, `alg:ttc`'s charged cost is at most `m · n⁴ · (2⁴²·volFac + 2⁶²·rfac·(R²/γ²)
  ·log(2R)·(Θ+1))`, written out as explicit arithmetic in `ε`, `δ`, the run's own geometry
  and `m = |toDNFd (preprocess atoms φ)|`.  The guard is discharged at the run's own
  geometry by `Ttc.PricedHeadline.all_ttc_cost_le_quartic_at_run`, which leaves visible the
  two binders nothing in this repository proves — the warm start `M ≤ (2R)ⁿ` and `2⁻ⁿ ≤ ε'`.
  It guards this conjunct only, so the accuracy half stays unconditional.

⚠ **The run does not execute the two oracles being priced.**  Correctness, not efficiency:
nothing here proves `TTC` runs in `O(m·n⁴)`.  See this file's docstring, the boxed warning
in `Ttc/Exec/PricedHeadline.lean`, and `AUDIT.md` §1e. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- (accuracy) the estimate is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[r ← ttc atoms φ ε δ (cvVolPriceAt atoms φ ε δ) (hrSampPriceAt atoms φ ε δ);
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) at any `(R, γ)` bounding the fixed sampling price quartically, almost
    -- every run is charged at most `m·n⁴·(2⁴²·volFac + 2⁶²·rfac·(R²/γ²)·log(2R)·(Θ + 1))`
    (∀ R γ : ℝ, 1 ≤ R → 0 < γ →
      ((hrSampPriceAt atoms φ ε δ : ℕ) : ℝ)
          ≤ 2 ^ 62 * (n : ℝ) ^ 4 * canonRfac (toDNFd (preprocess atoms φ))
              * (R ^ 2 / γ ^ 2) * Real.log (2 * R) →
      All[r ← ttc atoms φ ε δ (cvVolPriceAt atoms φ ε δ) (hrSampPriceAt atoms φ ε δ);
        (r.2 : ℝ) ≤
          ((toDNFd (preprocess atoms φ)).length : ℝ) * (n : ℝ) ^ 4
            * (2 ^ 42
                  * ((canonRfac (toDNFd (preprocess atoms φ)) + 1)
                      * Real.log (8 / (algBlock atoms φ ε δ).epsPrime ^ 2)
                      * ((1 + Real.log (1 + (n : ℝ)
                            * ((algGamma atoms φ ε δ)⁻¹
                                * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ))
                                    (preprocess atoms φ))) ^ 2)) ^ 4
                          * Real.log (1 / (algBlock atoms φ ε δ).deltaPrime)
                          / ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10) ^ 3))
                + 2 ^ 62 * canonRfac (toDNFd (preprocess atoms φ)) * (R ^ 2 / γ ^ 2)
                    * Real.log (2 * R)
                    * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                        + 15 * (Real.log (15 / (2 * δ))
                            + Real.log ((toDNFd (preprocess atoms φ)).length))
                        + 1))]) :=
  ⟨(ttc_volume_estimate_parametric atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos _ _).1,
    fun R γ hR1 hγ0 hcS =>
      PricedHeadline.all_ttc_cost_le_quartic atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos _ _
        (2 ^ 42) _ _ R γ (by norm_num)
        (PricedHeadline.zero_le_volFac atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1)
        (PricedHeadline.one_le_canonRfac atoms φ ε hε0 hε1 hn hφ hpos) hR1 hγ0
        (PricedHeadline.cvPrice_le atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1) hcS⟩

#print axioms ttc_volume_estimate

end Ttc
