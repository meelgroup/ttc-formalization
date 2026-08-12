/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Program
import Ttc.Exec.PricedHeadline

/-!
# The main theorem: `thm:volumettc` + `thm:runtime` for `TTC(F, ε, δ)`

The **statement layer**: one theorem, `Ttc.ttc_volume_estimate`, and nothing else — no
definition, no auxiliary lemma.  The accuracy half comes from
`Ttc.ttc_accuracy_pairLaw`; the running-time half is
`Ttc.PricedHeadline.all_ttc_cost_le_quartic` (`Ttc/Exec/PricedHeadline.lean`).

Both conjuncts speak about **the same run**, drawn from the one measure

    ttc atoms φ ε δ cVol cSample : Measure (ℝ × ℕ)

defined in `Model/Pseudocode`: accuracy about `r.1`, running time about `r.2`.  This
mirrors `ApproxNFA.countNFAM A n ε δ : PMF (ℝ × ℕ)`.

Nine binders — `atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos`.  Among them there is no
interpretation, no parameter block, no converter, no oracle, no precision, no
inscribed-ball data and no boundedness hypothesis.

`Pr[p ← μ; E p]` is `(μ {p | E p}).toReal` and `All[p ← μ; E p]` is `∀ᵐ p ∂μ`, both from
`Monadic/MeasurePr`.

Audit path: `Model/`'s four files, `Ttc/Probability/`'s four, and `Ttc/Geometry/`.
`#modelClosureOfType Ttc.ttc_volume_estimate` (`Audit/ClosureCheck`) fails the build if
any constant in this theorem's *type* is defined outside them — which is why the two
prices below are spelled out as arithmetic rather than named: `Ttc.ttcVolPriceCVAlg` and
`Ttc.ttcSampPriceHR` live in `Ttc/Exec/`, so **naming** either one in the type would turn
the check red.  The expressions are `Ttc.ttcVolPriceCVAlg_model`'s and
`Ttc.ttcSampPriceHR_model`'s right-hand sides, each equal to its price by `rfl`.

## ⚠ THE PRICES ARE NOW FIXED — AND THEY ARE NOT THE RUN'S OWN PRICES ⚠

This theorem used to quantify over two per-call prices `cVol cSample : ℕ`.  It no longer
does: the volume slot is fixed at the **Cousins–Vempala** operation price and the
sampling slot at the **hit-and-run** per-draw price, both evaluated at `(atoms, φ, ε, δ)`,
so that the running-time side can read `m · n⁴ · (…)`.

**`Ttc.ttc` executes neither of those two oracles.**  Its bundle `Ttc.algOracles`
(`Model/Pseudocode`) is a closed term over `Ttc.mcVol` — hit-and-miss Monte Carlo — whose
sampling law is the **lazy ball walk**.  The prices the modelled run can be *shown* to pay
are `Ttc.ttcVolPrice` (`Exec/PriceList`, justified by `Ttc.ttcVolCoins_le_ttcVolPrice`) and
`Ttc.ttcSampPrice` (`Exec/SamplePrice`, justified by `Ttc.ttcSampleSteps_le_ttcSampPrice`),
and both are **exponential in `n`**.  Charging the two numbers below is legal arithmetic
and nothing more — `cVol`/`cSample` are per-call *unit prices* in `Ttc.runCost`'s fold and
the call **counts** are oracle-independent (`m` volume calls, `≤ Θ+1` samples each) — but
it is a **modelling choice, not a costing of this run**.  No lemma anywhere dominates
`Ttc.ttcVolCoins` or `Ttc.ttcSampleSteps` by the numbers below, and for the sampler there
cannot be one (`Exec/SampPriceHR`, "What is *not* here").  Read the boxed warning at the
head of `Ttc/Exec/PricedHeadline.lean` before quoting anything from here.

**The unconditional, price-parametric statement has not been lost.**  It is
`Ttc.ttc_volume_estimate_parametric` (`Ttc/Exec/PricedHeadline.lean`), kept character for
character, and it — not this theorem — is what `Ttc/Exec/TheoremPoly.lean` and
`Ttc/Witness/FullTwoCube.lean` consume.  The fixed-price form below does **not** imply it.

## What is conditional, and what is not

* the **accuracy** conjunct is **unconditional** under the nine binders, exactly as before;
* the **running-time** conjunct is **guarded**: `∀ R γ, 1 ≤ R → 0 < γ → (the hit-and-run
  price is ≤ 2⁶²·n⁴·rfac·(R²/γ²)·log(2R)) → …`.  The guard is discharged at the run's own
  geometry — `R = Ttc.ttcSampDiamPrice`, `γ = Ttc.ttcSampInradius` — by
  `Ttc.ttcSampPriceHR_le_quartic`, which itself carries two binders **nothing in this
  repository proves**: the warm start `M ≤ (2R)ⁿ` and the regime condition `2⁻ⁿ ≤ ε'`.
  Guarding the runtime conjunct rather than adding those to the theorem's binder list is
  deliberate: it keeps the accuracy half free of an unwitnessed hypothesis, so
  `Ttc/Witness/FullTwoCube.lean` can still witness it.

The volume side needs **no** guard: `Ttc.PricedHeadline.cvPrice_le` discharges it from the
nine binders alone.  Its `2⁴²·n⁴` nevertheless assumes the warm start `M = 1` *inside* the
price, which is nowhere proved.

**Nothing anywhere proves that `TTC` runs in `O(m·n⁴)`.**  The hit-and-run step count is
meaningful only under `Ttc.HitAndRunTheorem11Input` (assumed, inhabited nowhere); the
Cousins–Vempala per-draw charge rests on `thm:iso`, an unproved binder of
`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`; and the charged cost is an
**undercount** — one unit per oracle call, nothing for the arithmetic inside a call, the
rejection rounds, or `alg:ttc`'s lines 32–42 loops.  The `n⁴` also holds only where the
body is temperature-scale (`R = O(σ)`); in the Cousins–Vempala regime `R ≍ σ√n` it is `n⁵`,
and `Arlib.MarkovChains.exists_halfspace_max_lt` shows the obvious route to recovering the
missing `√n` is **false**, not merely open.

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
open scoped Pointwise

set_option maxHeartbeats 4000000 in
/-- **`thm:volumettc` + `thm:runtime`, at two FIXED per-call prices.**  `TTC` is run on
`F = (atoms, φ)` at accuracy `ε` and confidence `δ`; both halves speak about the same run,
drawn from `Ttc.ttc` at the Cousins–Vempala volume price and the hit-and-run sampling
price.

* **Accuracy.** `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, at the **user's own**
  `Vol(F)`, **unconditionally** under the nine binders.  The output is
  `Model/Pseudocode`'s `Ttc.ttcRun`, which takes no oracle argument.
* **Running time.** `All[…]` is `∀ᵐ`, with **no termination hypothesis**: the absorption
  loops halt `Ttc.ttc`-almost surely.  Under the guard `1 ≤ R`, `0 < γ` and "the fixed
  sampling price is at most `2⁶²·n⁴·rfac·(R²/γ²)·log(2R)`", the charged cost is at most
  `m · n⁴ · (2⁴²·volFac + 2⁶²·rfac·(R²/γ²)·log(2R)·(Θ+1))`, written out as explicit
  arithmetic in `ε`, `δ`, the run's own geometry and `m = |toDNFd (preprocess atoms φ)|`.

⚠ **The run does not execute the two oracles being priced** — see this file's docstring and
the boxed warning in `Ttc/Exec/PricedHeadline.lean`.  The price-parametric, unconditional
form is `Ttc.ttc_volume_estimate_parametric`.  Correctness, not efficiency: nothing here
proves `TTC` runs in `O(m·n⁴)`.  See also `AUDIT.md` §1e. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- (accuracy) the estimate is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[r ← ttc atoms φ ε δ
            -- `cVol` := the Cousins–Vempala per-call volume price
            ((⌈4 * Arlib.MarkovChains.lsThreshold 1 (Real.log 2 / (5120 * (n : ℝ)))
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
                              / ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10)⌉₊ + 1))))
            -- `cSample` := the hit-and-run per-draw price
            ((⌊2 ^ 56 * (n : ℝ) ^ 2 * ((1 +
                  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
                  (canonRfac (toDNFd (preprocess atoms φ))) /
                  (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) *
                  Metric.diam (latticeScale (algPrec atoms φ ε δ) •
                  sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2 /
                  (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
                  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
                  (canonRfac (toDNFd (preprocess atoms φ)))) ^ 2 *
                  Real.log (8 * (((1 +
                  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
                  (canonRfac (toDNFd (preprocess atoms φ))) /
                  (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) ^ n *
                  (latticeScale (algPrec atoms φ ε δ) ^ n *
                  (algScale atoms φ ε δ ^ n * volSol (atomSet atoms) φ))) /
                  (volume (Metric.ball (0 : Space n)
                  (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
                  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
                  (canonRfac (toDNFd (preprocess atoms φ)))))).toReal) /
                  ((algBlock atoms φ ε δ).epsPrime / (4 * (2 * ((1 +
                  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
                  (canonRfac (toDNFd (preprocess atoms φ))) /
                  (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) *
                  Metric.diam (latticeScale (algPrec atoms φ ε δ) •
                  sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)))) ^ n)) ^ 2)⌋₊
                + 1 + 2)
              * ⌈(n : ℝ) * canonRfac (toDNFd (preprocess atoms φ))⌉₊);
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) at any `(R, γ)` bounding the fixed sampling price quartically, almost
    -- every run is charged at most `m·n⁴·(2⁴²·volFac + 2⁶²·rfac·(R²/γ²)·log(2R)·(Θ + 1))`
    (∀ R γ : ℝ, 1 ≤ R → 0 < γ →
      (((⌊2 ^ 56 * (n : ℝ) ^ 2 * ((1 +
              Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
              (canonRfac (toDNFd (preprocess atoms φ))) /
              (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) *
              Metric.diam (latticeScale (algPrec atoms φ ε δ) •
              sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2 /
              (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
              Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
              (canonRfac (toDNFd (preprocess atoms φ)))) ^ 2 *
              Real.log (8 * (((1 +
              Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
              (canonRfac (toDNFd (preprocess atoms φ))) /
              (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) ^ n *
              (latticeScale (algPrec atoms φ ε δ) ^ n *
              (algScale atoms φ ε δ ^ n * volSol (atomSet atoms) φ))) /
              (volume (Metric.ball (0 : Space n)
              (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
              Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
              (canonRfac (toDNFd (preprocess atoms φ)))))).toReal) /
              ((algBlock atoms φ ε δ).epsPrime / (4 * (2 * ((1 +
              Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
              (canonRfac (toDNFd (preprocess atoms φ))) /
              (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) *
              Metric.diam (latticeScale (algPrec atoms φ ε δ) •
              sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)))) ^ n)) ^ 2)⌋₊
            + 1 + 2)
          * ⌈(n : ℝ) * canonRfac (toDNFd (preprocess atoms φ))⌉₊ : ℕ) : ℝ)
        ≤ 2 ^ 62 * (n : ℝ) ^ 4 * canonRfac (toDNFd (preprocess atoms φ))
            * (R ^ 2 / γ ^ 2) * Real.log (2 * R) →
      All[r ← ttc atoms φ ε δ
            ((⌈4 * Arlib.MarkovChains.lsThreshold 1 (Real.log 2 / (5120 * (n : ℝ)))
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
                              / ((algBlock atoms φ ε δ).epsPrime ^ 2 / 10)⌉₊ + 1))))
            ((⌊2 ^ 56 * (n : ℝ) ^ 2 * ((1 +
                  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
                  (canonRfac (toDNFd (preprocess atoms φ))) /
                  (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) *
                  Metric.diam (latticeScale (algPrec atoms φ ε δ) •
                  sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ))) ^ 2 /
                  (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
                  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
                  (canonRfac (toDNFd (preprocess atoms φ)))) ^ 2 *
                  Real.log (8 * (((1 +
                  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
                  (canonRfac (toDNFd (preprocess atoms φ))) /
                  (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) ^ n *
                  (latticeScale (algPrec atoms φ ε δ) ^ n *
                  (algScale atoms φ ε δ ^ n * volSol (atomSet atoms) φ))) /
                  (volume (Metric.ball (0 : Space n)
                  (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ +
                  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
                  (canonRfac (toDNFd (preprocess atoms φ)))))).toReal) /
                  ((algBlock atoms φ ε δ).epsPrime / (4 * (2 * ((1 +
                  Arlib.KV97.kappaOf (Arlib.KV97.cOf (algBlock atoms φ ε δ).epsPrime)
                  (canonRfac (toDNFd (preprocess atoms φ))) /
                  (latticeScale (algPrec atoms φ ε δ) * algGamma atoms φ ε δ)) *
                  Metric.diam (latticeScale (algPrec atoms φ ε δ) •
                  sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)))) ^ n)) ^ 2)⌋₊
                + 1 + 2)
              * ⌈(n : ℝ) * canonRfac (toDNFd (preprocess atoms φ))⌉₊);
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
