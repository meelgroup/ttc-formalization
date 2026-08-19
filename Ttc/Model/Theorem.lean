/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Program
import Ttc.Exec.PricedHeadline
import Ttc.Exec.SamplePrice
import Ttc.Exec.TtcSlowRuntimePerPhase

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
open scoped ENNReal BigOperators Classical

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
    -- (running time) almost every run is charged at most
    -- `m · (C_vol + C_sample·(Θ + 1))`, at the two prices the run ACTUALLY pays.
    -- Both are written out: `C_vol` is the coin count of `Ttc.mcVol`, the hit-and-miss
    -- Monte-Carlo oracle `Ttc.algOracles` is built over, and `C_sample` is
    -- `Ttc.mixStepsBound` at the run's own arguments.  BOTH ARE EXPONENTIAL IN `n` —
    -- visible here as the `^ n` of the first and the `4 ^ n`, `^ (2 * n)`, `^ (4 * n)`
    -- of the second.  Nothing is hidden behind a name.
    (All[r ← ttc atoms φ ε δ;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ)
          * (((
          ⌈((algGamma atoms φ ε δ)⁻¹
                * Metric.diam (sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)) + 1) ^ n
              / ((algBlock atoms φ ε δ).epsPrime ^ 2 * (algBlock atoms φ ε δ).deltaPrime)⌉₊ + 1 : ℕ) : ℝ)
              + ((
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
            (canonRfac (toDNFd (preprocess atoms φ))))) ^ (4 * n)) + 1⌉₊ : ℕ) : ℝ)
              * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                  + 15 * (Real.log (15 / (2 * δ))
                      + Real.log ((toDNFd (preprocess atoms φ)).length))
                  + 1))]) :=
  ⟨(ttc_volume_estimate_parametric atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos _ _).1,
    (ttc_volume_estimate_parametric atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos _ _).2⟩

/-- **`thm:volumettc` + `thm:runtime`, at the oracles the paper actually specifies.**

`Ttc.ttc_volume` above is about `Ttc.ttc`, whose volume oracle is `Ttc.mcVol` — hit-and-miss
Monte Carlo — and whose sampler is the lazy ball walk.  Those are *reference* oracles: correct,
and exponential in `n`, as its own statement now shows.

This is the same guarantee for the constructed ones:

* **volume** — `slowPerPhaseImplementation.algorithm n`, the Cousins–Vempala Gaussian-cooling
  estimator (`sections/analysis.tex`, `cor:vol`);
* **sampling** — `Ttc.kv97HybridKernel`: hit-and-run at `1100 ≤ n` (`cor:linf`), lazy ball
  walk below.

Both conjuncts are about the one law that executes them.  No oracle, certificate,
implementation or cost binder; axioms `[propext, Classical.choice, Quot.sound]`.

⚠ **Three things this is not.**

1. **Not the paper's number.**  The envelope is `Õ(m·n⁴·ρ⁶/ε²)` in *membership-query* units,
   not `O(m·n⁵·ρ²·r_max)`, and the two are not in the same units until the `⌈n·rfac⌉₊` charge
   of `ttc_volume_runtime_perPhase_ops` is applied.  The `ρ` exponent is unsettled.  See
   `lean/PLAN-SHAPE.md` §5.
2. **Not uniform in the dimension.**  At `1100 ≤ n` the sampler is hit-and-run and the
   transition bound is polynomial.  For `21 ≤ n < 1100` it is the ball walk's own bound, with
   `4 ^ n` and a `(radius ratio)^(4n)`; `n` is bounded there, so that is a constant and not an
   asymptotic obstruction — but an astronomical one.  Proved in both directions in
   `Ttc/Exec/SamplerEnvelopeShape.lean`.  Removing it is one lemma: `lean/PLAN-SPHERECAP.md`.
3. **Not inside the four-file audit surface.**  Its statement names the construction — 637
   constants across 108 modules — so `#modelClosureOfType` does not hold of it and is not
   claimed.  `Ttc.ttc_volume` keeps that promise for accuracy. -/
theorem ttc_volume_runtime {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : 21 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    let deltaRun := 4 * δ / 5
    let hn1 : 1 ≤ n := le_trans (by norm_num) hn
    let I := Ttc.TtcSlowRuntimePerPhase.slowPerPhaseImplementation
    let V := I.algorithm n
    letI : NeZero n := ⟨Nat.ne_of_gt hn1⟩
    let P := Ttc.TTCSourceSharpOperationalFinal.canonicalCappedPolyHybridPlugin
      atoms φ ε deltaRun V hε0 hε1 hn1 hφ hpos
    (1 - δ ≤ (Ttc.TTCSourceSharpOperationalTheorem.canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr ε (volSol (atomSet atoms) φ)}) ∧
    ((∫⁻ r, r.2 ∂Ttc.TTCSourceSharpOperationalTheorem.canonicalFullOperationalLaw V P) ≤
      Ttc.CVShaped.shapedVolumeQueryEnvelopeAt I atoms φ ε deltaRun
          (fun j ↦ (Ttc.TtcCircumRadius.circumR (interior
            (Ttc.TTCCVExpectedImplementation.callBody atoms φ ε deltaRun j))) ^ 2) +
        Ttc.TTCSourceSharpOperationalFinal.canonicalCappedSampleQueryEnvelope
          atoms φ ε deltaRun) :=
  Ttc.TtcSlowRuntimePerPhase.ttc_volume_runtime_perPhase atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos

#print axioms ttc_volume_runtime

#print axioms ttc_volume

end Ttc
