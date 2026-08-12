/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Pseudocode
import Arlib.MarkovChains.Continuous.HitAndRunMixing
import Arlib.Convexity.GaussianCooling.PhaseSchedule

/-!
# `Prices/Fixed`: the two numbers `Ttc.ttc_volume_estimate` charges

Two `def`s and nothing else — the Cousins–Vempala per-call volume price and the hit-and-run
per-draw sampling price, each written in `Ttc/Model/` vocabulary at the algorithm's own
inputs `(atoms, φ, ε, δ)`.

## Why this directory exists

`Ttc.ttc_volume_estimate` fixes both per-call prices rather than quantifying over them.
The prices themselves are derived in `Ttc/Exec/` (`Ttc.ttcVolPriceCVAlg`,
`Ttc.ttcSampPriceHR`), and `#modelClosureOfType` tests a constant's **defining module**, so
naming either one in the headline's type turns the check red.  Until now the headline
worked around that by spelling both expressions out **inline**, three times over, which
made its type ~150 lines and the file unreadable — the check stayed green while the thing
it protects, an auditable statement, was lost.

This file is the honest version of that workaround: the same two expressions, named once,
in a directory `Ttc.Audit.auditSurface` admits **explicitly**.  See `Audit/ClosureCheck`'s
section docstring for the argument and for the bound on what may go here — *definitions
only, no `Prop`s, and nothing but these two prices*.  It is a real widening of the
reader-facing promise, traded for a headline a human can read; the two `rfl` bridges
`Ttc.cvVolPriceAt_eq` and `Ttc.hrSampPriceAt_eq` (`Exec/VolPriceCVAlg`) are what keep the
names from standing in for the analysis (`CLAUDE.md` §13).

## ⚠ Neither number is a price this run is proved to pay ⚠

`Ttc.ttc`'s oracle bundle `Ttc.algOracles` is a closed term over `Ttc.mcVol` —
hit-and-miss Monte Carlo — whose sampling law is the lazy ball walk.  The prices the
modelled run **is** shown to pay are `Ttc.ttcVolPrice` (`Exec/PriceList`) and
`Ttc.ttcSampPrice` (`Exec/SamplePrice`), and both are exponential in `n`.  `cVol`/`cSample`
are unit multipliers in `Ttc.stepCost` (`stepCost cVol cSample N = cVol + cSample * N`), so
substituting *any* pair of naturals yields a bound of the headline's shape — at `0` it
yields `r.2 ≤ 0`.  Fixing them at the two numbers below is a **modelling choice, not a
costing of this run**.  Read `Ttc/Exec/PricedHeadline.lean`'s boxed warning before quoting
the headline's running-time conjunct.
-/

namespace Ttc

open MeasureTheory Set
open scoped Pointwise

variable {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)

/-- **The Cousins–Vempala per-call volume price at the run's own data.**  The right-hand
side of `Ttc.ttcVolPriceCVAlg_model`, verbatim: `Ttc.CVCost.cvVolumeOpsPrice` unfolded to
`Ttc/Model/` vocabulary, so that the headline may name it.  Equal to
`Ttc.ttcVolPriceCVAlg` by `rfl` — `Ttc.cvVolPriceAt_eq` (`Exec/VolPriceCVAlg`).

Reading it: `(⌈4·lsThreshold⌉₊ + 3)` transitions at `⌈n·r⌉₊` operations each, times the
number of Cousins–Vempala draws — `(⌈log(1/δ')/2(4/5−1/2)²⌉₊ + 1)` per phase across
`Ttc.Arlib.GaussianCooling.coolPhases` phases.

⚠ Not a price `Ttc.ttc` is proved to pay; see this module's docstring. -/
noncomputable def cvVolPriceAt : ℕ :=
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

/-- **The hit-and-run per-draw sampling price at the run's own data.**  The right-hand side
of `Ttc.ttcSampPriceHR_model`, verbatim: `Ttc.SamplerCost.samplePrice` unfolded to
`Ttc/Model/` vocabulary.  Equal to `Ttc.ttcSampPriceHR` by `rfl` — `Ttc.hrSampPriceAt_eq`
(`Exec/VolPriceCVAlg`).

Reading it: `⌊2⁵⁶·n²·(R²/γ²)·log(8M/ν²)⌋₊ + 1` transitions plus `2` post-processing units,
at `⌈n·r⌉₊` operations each, with `ν = ε'/(4·(2R)ⁿ)` the worst-case TV tolerance, `R` the
inflated body's diameter and `γ` its inradius.

⚠ Not a price `Ttc.ttc` is proved to pay, and for this one there provably cannot be such a
lemma — see `Exec/SampPriceHR`, "What is *not* here", and this module's docstring. -/
noncomputable def hrSampPriceAt : ℕ :=
  (⌊2 ^ 56 * (n : ℝ) ^ 2 * ((1 +
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
    sol (atomSet (algAtoms atoms φ ε δ)) (preprocess atoms φ)))) ^ n)) ^ 2)⌋₊ + 1 + 2) *
    ⌈(n : ℝ) * canonRfac (toDNFd (preprocess atoms φ))⌉₊

end Ttc
