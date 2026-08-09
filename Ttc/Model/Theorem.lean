/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Inputs

/-!
# The main theorem: `thm:volumettc` + `thm:runtime` for `TTC(F, ε, δ)`

One theorem, and no proof to work through — it is one application of
`Ttc.ttc_volume_vol` (`Exec/Inputs`).

Audit path — `Model/`, then stop: `Model/Prelude` (the vocabulary),
`Model/ProblemSetting` (what `Vol(F)` is and what `(1 ± ε)` means),
`Model/Pseudocode` (`alg:ttc`, transcribed line by line), this file.

`TTC` takes three inputs, so three inputs is what this statement takes: the
formula `F = (atoms, φ)`, the accuracy `ε`, the confidence `δ`.  There is **no
interpretation, no parameter block, no converter, no oracle and no precision**
among them: the four quantities the guarantee is about are `Ttc.runOracles`,
`Ttc.ttcRunOutput`, `Ttc.runRates` and `Ttc.runPrec` (`Exec/Inputs`), each a
closed term computed from `(atoms, φ, ε, δ)` — in particular `Ttc.runPrec` is
`GetPrecision`'s output `⌈log₁₀(γ/γ̂)⌉` (`alg:ttc` line 17), and the oracle bundle
is built from `Ttc.VolumeAlgorithm.monteCarlo` and the ball walk.  The
bundle-level versions, whose types name the *assumed* `T.O` and `T.ρ`, are
`Ttc.TtcProb.volume_estimate` and `Ttc.TtcProb.runtime` (`Ttc/Estimate.lean`).

Elsewhere, deliberately: which lemma discharges which former binder, in
`Exec/Inputs.lean`; how the sampler-level regime condition is derived from `hvol`,
in `Exec/RegimeMain.lean`; why no hypothesis of that kind can be dropped — it is
*proved* independent — in `Exec/Regime.lean` and README finding 20; non-vacuity in
`Witness/Headline.lean`; the audit in `AUDIT.md` §1e–§1f.

`sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ttc

open MeasureTheory Set

/-- **`thm:volumettc` + `thm:runtime`.**  `TTC` is run on `F = (atoms, φ)` at
accuracy `ε` and confidence `δ`.

* **Accuracy.**  `Pr[ output ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, over the volume coins
  (law `Ttc.MonteCarlo.coins n`) and the sample coins (law `Ttc.trajLaw`).
* **Running time.**  On every run, `alg:ttc`'s charged cost
  `m · (C_vol + C_sample · Thresh)`, under `Ttc.Terminates`.

Seven hypotheses besides the inputs and the parameter range, every one a condition
on the **input**: `hφ` the formula is negation-free (finding 5); `hbdd` its solution
set is bounded (*necessary* — otherwise `Vol(F) = ∞`); `hcoeff` no atom is
degenerate; `cen`/`gammaHat`/`hgammaHat`/`ball_subset` the inscribed ball `alg:ttc`
computes by an LP; and `hvol : Thresh/4 ≤ Vol(F)`, the regime condition.

`hvol` is **not** removable — `Ttc.Box.big_not_derivable` proves the restriction is
real, and it is the paper's own unstated `j* ≥ 1` (`sections/analysis.tex:284`,
README finding 20). What it is not is opaque: `Ttc.big_of_volume` derives the
sampler-level condition from this one scalar inequality about `Vol(F)`.

Correctness, not efficiency: both oracle routes are exponential in `n`. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))
    (hcoeff : ∀ j : FacetIndex (toDNFd φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNFd φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region (atomSet atoms) i.val)
    (hvol : (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).thresh / 4
      ≤ volSol (atomSet atoms) φ) :
    -- (accuracy) the output is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      (∫⁻ c, trajLaw (runRates atoms φ ε δ hε0 hε1 hn hφ hbdd cen gammaHat c)
            {t | ttcRunOutput atoms φ ε δ hε0 hε1 hn hφ hbdd cen gammaHat c t
              ∈ relErr ε (volSol (atomSet atoms) φ)}
          ∂(MonteCarlo.coins n)).toReal)
    ∧
    -- (running time) `alg:ttc`'s charged cost, on every run, under `Ttc.Terminates`
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (runCount atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd).thresh →
      Terminates (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd)
          (runOracles atoms φ ε δ hε0 hε1 hn hφ hbdd cen gammaHat c t) (toDNFd φ) →
      runCost (inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd)
          (runOracles atoms φ ε δ hε0 hε1 hn hφ hbdd cen gammaHat c t)
          cVol cSample (runPrec atoms φ ε δ hε0 hε1 hn hφ hbdd gammaHat) (toDNFd φ)
        ≤ (toDNFd φ).length * (cVol + cSample * thr)) :=
  ttc_volume_vol atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hbdd hcoeff
    cen gammaHat hgammaHat ball_subset hvol

#print axioms ttc_volume_estimate

end Ttc
