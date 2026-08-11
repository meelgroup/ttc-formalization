/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Program

/-!
# The main theorem: `thm:volumettc` + `thm:runtime` for `TTC(F, ε, δ)`

The **statement layer**: one theorem, `Ttc.ttc_volume_estimate`, and nothing else — no
definition, no auxiliary lemma, no proof to work through.  The accuracy half is
`Ttc.ttc_accuracy_pairLaw` and the running-time half `Ttc.all_ttcPairLaw_cost_le`.

Both conjuncts speak about **the same run**, drawn from the one measure

    ttc atoms φ ε δ cVol cSample : Measure (ℝ × ℕ)

defined in `Model/Pseudocode`: accuracy about `r.1`, running time about `r.2`.  This
mirrors `ApproxNFA.countNFAM A n ε δ : PMF (ℝ × ℕ)`.

Eleven binders — `atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos` — plus the two per-call
charges.  Among them there is no interpretation, no parameter block, no converter, no
oracle, no precision, no inscribed-ball data and no boundedness hypothesis.

`Pr[p ← μ; E p]` is `(μ {p | E p}).toReal` and `All[p ← μ; E p]` is `∀ᵐ p ∂μ`, both from
`Monadic/MeasurePr`.

Audit path: `Model/`'s four files, `Ttc/Probability/`'s four, and `Ttc/Geometry/`.
`#modelClosureOfType Ttc.ttc_volume_estimate` (`Audit/ClosureCheck`) fails the build if
any constant in this theorem's *type* is defined outside them.

[`AUDIT.md`](../../AUDIT.md) §1e is written to be read alongside this file, and carries
what is deliberately not restated here: why `cVol`/`cSample` stay parametric and why the
prices they stand for are **exponential in `n`** rather than the paper's `O(n⁴)`/`O(n³)`;
which quantifier the running-time half uses and why the pointwise form is false; why this
is a `Measure` and not a `PMF`; the definitional closure; the three preprocessing steps
the headline certifies `alg:ttc` *plus*; the two residual hypotheses `hφ` and `hpos`; and
that `hbdd` was derived rather than dropped (§1h).
-/

namespace Ttc

open MeasureTheory Set
open Ttc.Monadic

/-- **`thm:volumettc` + `thm:runtime`.**  `TTC` is run on `F = (atoms, φ)` at accuracy
`ε` and confidence `δ`; both halves speak about the same run, drawn from `Ttc.ttc`.

* **Accuracy.** `Pr[ TTC(F, ε, δ) ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, at the **user's own**
  `Vol(F)`.  The output is `Model/Pseudocode`'s `Ttc.ttcRun`, which takes no oracle
  argument.
* **Running time.** `All[…]` is `∀ᵐ`, with **no termination hypothesis**: the absorption
  loops halt `Ttc.ttc`-almost surely.  `alg:ttc`'s charged cost is at most
  `m · (cVol + cSample · (Θ + 1))`, written out as explicit arithmetic in `ε`, `δ` and
  `m = |toDNFd (preprocess atoms φ)|`.

Correctness, not efficiency: both oracle routes are exponential in `n`.  See `AUDIT.md`
§1e. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (cVol cSample : ℕ) :
    -- (accuracy) the estimate is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      Pr[r ← ttc atoms φ ε δ cVol cSample;
        r.1 ∈ relErr ε (volSol (atomSet atoms) φ)])
    ∧
    -- (running time) almost every run is charged at most `m·(cVol + cSample·(Θ + 1))`
    (All[r ← ttc atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤
        ((toDNFd (preprocess atoms φ)).length : ℝ)
          * ((cVol : ℝ) + (cSample : ℝ)
              * (41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
                  + 15 * (Real.log (15 / (2 * δ))
                      + Real.log ((toDNFd (preprocess atoms φ)).length))
                  + 1))]) := by
  rw [ttc_eq_ttcPairLaw]
  refine ⟨ttc_accuracy_pairLaw atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 cVol cSample, ?_⟩
  have h := all_ttcPairLaw_cost_le atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 cVol cSample
  simpa only [ttcComplexity_def] using h

#print axioms ttc_volume_estimate

end Ttc
