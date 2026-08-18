/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Program
import Ttc.Exec.PricedHeadline
import Ttc.Exec.SamplePrice

/-!
# The main theorem of the paper

`Ttc/Model/` describes the paper and nothing else: `Prelude` the preliminaries,
`ProblemSetting` the problem definition, `Pseudocode` the algorithm, and this file the main
theorem — `thm:volumettc` + `thm:runtime` in one statement, about `Ttc.ttc` itself.

**One theorem, two conjuncts, one run.**  `Ttc.ttc_volume` states accuracy and charged cost
for the *same* law: `Ttc.ttc atoms φ ε δ` (`Model/Pseudocode`), the algorithm's own law on
runs `r = (volume coins, trajectory)`, taking `TTC`'s own four inputs and nothing else — no
interpretation, no parameter block, no oracle argument, no precision argument.  The accuracy
conjunct is about `r.1`, the cost conjunct about `r.2`.  The statement is written out here in
full — this is the **audit surface** — and the proof is discharged by reference to the
development (`Ttc.ttc_volume_estimate_parametric` and
`Ttc.PricedHeadline.all_ttc_cost_le_quartic`, both in `Ttc/Exec/PricedHeadline.lean`).

## What it says

* **Accuracy.**  `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, at the user's own `Vol(F)`,
  **unconditionally** under the nine binders.
* **Charged cost.**  `All[…]` is `∀ᵐ`, with **no termination hypothesis**: the absorption
  loops halt `Ttc.ttc`-almost surely.  At any `(R, γ)` bounding the fixed sampling price
  quartically, the charged cost is at most `m·n⁴·(2⁴²·volFac + 2⁶²·rfac·(R²/γ²)·log(2R)·(Θ+1))`,
  written out as explicit arithmetic in `ε`, `δ`, the run's own geometry and
  `m = |toDNFd (preprocess atoms φ)|`.  The guard is discharged at the run's own geometry by
  `Ttc.PricedHeadline.all_ttc_cost_le_quartic_at_run`, and it guards this conjunct only, so
  the accuracy half stays unconditional.

## ⚠ Which complexity this is, and which it is not

**This run does not execute the two oracles being priced.**  `Ttc.ttc`'s cost coordinate is
charged at two *fixed* prices — the Cousins–Vempala and hit-and-run numbers — which are not
prices this run is proved to pay.  Nothing here proves `TTC` runs in `O(m·n⁴)`.  Read the boxed
warning in `Ttc/Exec/PricedHeadline.lean` and `AUDIT.md` §1e before quoting the cost conjunct.

The repository's **proved** polynomial figure is a different statement about a different
object: `Ttc.TtcSlowRuntimePerPhase.ttc_volume_runtime_perPhase` bounds the expected query
cost of `canonicalFullOperationalLaw`, the law that **actually executes** the constructed
volume subroutine `slowPerPhaseImplementation.algorithm n`, unconditionally and with no
oracle, certificate, implementation or cost-side binder, at

```
                    Õ( m · n⁶ · ρ⁸ / ε⁴ )
```

— charged cost, per polytope, `ρ` the aspect ratio.  That is **not** the paper's
`O(m · n⁵ · ρ² · r_max)`; the gap and every route examined for closing it are recorded in
`AUDIT.md` §0g and `PLAN-RETRYENV.md`.  It is stated for the operational law rather than for
`Ttc.ttc` because that is the object for which executing the real oracle is proved; carrying
it back to `Ttc.ttc` is exactly the accounting step this repository has not taken.
-/

namespace Ttc

open MeasureTheory Set
open Ttc.Monadic

/-- **`thm:volumettc` + `thm:runtime`, at two fixed per-call prices.**  `TTC` is run on
`F = (atoms, φ)` at accuracy `ε` and confidence `δ`; both halves speak about the same run.

* **Accuracy.** `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, at the **user's own**
  `Vol(F)`, **unconditionally** under the nine binders.  The output is
  `Model/Pseudocode`'s `Ttc.ttcRun`, which takes no oracle argument.
* **Charged cost.** `All[…]` is `∀ᵐ`, with **no termination hypothesis**.  At any `(R, γ)`
  bounding the fixed sampling price quartically, `alg:ttc`'s charged cost is at most
  `m · n⁴ · (2⁴²·volFac + 2⁶²·rfac·(R²/γ²)·log(2R)·(Θ+1))`.

⚠ **The run does not execute the two oracles being priced.**  Correctness, not efficiency:
nothing here proves `TTC` runs in `O(m·n⁴)`.  The repository's proved polynomial bound is
`Ttc.TtcSlowRuntimePerPhase.ttc_volume_runtime_perPhase`, at `Õ(m·n⁶·ρ⁸/ε⁴)`, and it is about
the operational law that actually executes the constructed oracle — see this file's module
docstring. -/
theorem ttc_volume {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- (accuracy) the estimate is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[r ← ttc atoms φ ε δ;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) at any `(R, γ)` bounding the fixed sampling price quartically, almost
    -- every run is charged at most `m·n⁴·(2⁴²·volFac + 2⁶²·rfac·(R²/γ²)·log(2R)·(Θ + 1))`
    (∀ R γ : ℝ, 1 ≤ R → 0 < γ →
      ((hrSampPriceAt atoms φ ε δ : ℕ) : ℝ)
          ≤ 2 ^ 62 * (n : ℝ) ^ 4 * canonRfac (toDNFd (preprocess atoms φ))
              * (R ^ 2 / γ ^ 2) * Real.log (2 * R) →
      All[r ← ttc atoms φ ε δ;
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


#print axioms ttc_volume

end Ttc
