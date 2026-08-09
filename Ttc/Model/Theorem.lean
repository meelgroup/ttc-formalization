/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.CleanInput

/-!
# The main theorem: `thm:volumettc` + `thm:runtime` for `TTC(F, ε, δ)`

One theorem, and no proof to work through — it is one application of
`Ttc.ttc_volume_cleanInput` (`Exec/CleanInput`).

Audit path — `Model/`, then stop: `Model/Prelude` (the vocabulary),
`Model/ProblemSetting` (what `Vol(F)` is and what `(1 ± ε)` means),
`Model/Pseudocode` (`alg:ttc`, transcribed line by line), this file.

`TTC` takes three inputs, so three inputs is what this statement takes: the formula
`F = (atoms, φ)`, the accuracy `ε`, the confidence `δ`.  **Twelve binders in all**, and
among them there is no interpretation, no parameter block, no converter, no oracle, no
precision, no inscribed-ball data and no condition on the size of `Sol(F)`.  Everything
the guarantee is about is a closed term computed from `(atoms, φ, ε, δ)`:
`Ttc.runOracles`, `Ttc.ttcRunOutput`, `Ttc.runRates`, `Ttc.runPrec` (`Exec/Inputs`),
`Ttc.autoCen`/`Ttc.autoGamma` (`Exec/Inscribed`), `Ttc.runScale`/`Ttc.scaledAtoms`
(`Exec/Rescaled`) and `Ttc.cleanForm` (`Exec/Cleanup`).  In particular `Ttc.runPrec` is
`GetPrecision`'s output `⌈log₁₀(γ/γ̂)⌉` (`alg:ttc` line 17), and the oracle bundle is
built from `Ttc.VolumeAlgorithm.monteCarlo` and the ball walk.  The bundle-level
versions, whose types name the *assumed* `T.O` and `T.ρ`, are
`Ttc.TtcProb.volume_estimate` and `Ttc.TtcProb.runtime` (`Ttc/Estimate.lean`).

## What is certified is `alg:ttc` plus two preprocessing steps

Read this before quoting the statement.

* **A dilation** (`Exec/Rescaled`).  The printed algorithm sets `p ← 1` and only halves
  it, so its sketch is `Poisson(Λ)` with `Λ ≤ Vol(Sol F)`; on a body of volume `10⁻⁶` it
  draws `Pois(10⁻⁶)` points and returns `0`.  So the input is dilated by
  `Ttc.runScale` first and the estimate divided by `cⁿ`.  This **changes what the
  algorithm runs on**; `Ttc.Box.big_not_derivable` and README finding 20 are why it is
  needed.
* **A cleanup** (`Exec/Cleanup`).  Zero-normal atoms are constant-folded away.  This one
  is benign: `Ttc.sol_cleanForm` gives *exact set equality*, so nothing geometric moves.
  `Ttc.not_isDNFOf_cleanDNF` records why the formula has to move with the DNF rather
  than the DNF being cleaned in place.

## The three residual hypotheses, and what is known about each

* `hφ` — negation-free.  Independent of `hbdd` in **both** directions
  (`Ttc.Independence.exists_isBounded_not_isPositive`,
  `…exists_isPositive_not_isBounded`), so neither can replace the other.  Removable in
  principle, but at a bad price — see `Findings/OpenHalfspace.lean`.
* `hbdd` — bounded solution set.  *Necessary*: `Ttc.volSol` is an `ENNReal.toReal` and
  `toReal ⊤ = 0`, so an unbounded `Sol(F)` would certify "the output is ≈ 0"
  (finding 16).
* `hint` — every cube full-dimensional.  **Proved not derivable**
  (`Ttc.hint_not_derivable`, with `0 < Vol(F)` so the conclusion is not vacuous), and
  the null-set escape is blocked in principle: `lem:lattice` counts lattice points, which
  are themselves null (`Exec/Degenerate.lean`).

Non-vacuity: `Ttc.TwoCube.ttc_volume_estimate_two_cube_full` (`Witness/FullTwoCube.lean`).
The audit is `AUDIT.md` §1e–§1g.

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
    (hint : ∀ i : {c : Cube A // c ∈ toDNFd φ},
      (interior (region (atomSet atoms) i.val)).Nonempty) :
    (1 - δ ≤
      (∫⁻ c, trajLaw
            (runRates
              (scaledAtoms atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
                (autoGamma atoms (cleanForm atoms φ)))
              (cleanForm atoms φ) ε δ hε0 hε1 hn (isPositive_cleanForm atoms φ)
              (scaledBdd atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
                (autoGamma atoms (cleanForm atoms φ)))
              (fun i =>
                runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                      (isPositive_cleanForm atoms φ)
                      (cleanBdd atoms hφ hbdd hint) (autoGamma atoms (cleanForm atoms φ))
                  • autoCen atoms (cleanForm atoms φ) i)
              (runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                    (isPositive_cleanForm atoms φ)
                    (cleanBdd atoms hφ hbdd hint) (autoGamma atoms (cleanForm atoms φ))
                  * autoGamma atoms (cleanForm atoms φ)) c)
          {t | ttcRunOutput
                (scaledAtoms atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                  (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
                  (autoGamma atoms (cleanForm atoms φ)))
                (cleanForm atoms φ) ε δ hε0 hε1 hn (isPositive_cleanForm atoms φ)
                (scaledBdd atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                  (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
                  (autoGamma atoms (cleanForm atoms φ)))
                (fun i =>
                  runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                        (isPositive_cleanForm atoms φ)
                        (cleanBdd atoms hφ hbdd hint) (autoGamma atoms (cleanForm atoms φ))
                    • autoCen atoms (cleanForm atoms φ) i)
                (runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                      (isPositive_cleanForm atoms φ)
                      (cleanBdd atoms hφ hbdd hint) (autoGamma atoms (cleanForm atoms φ))
                    * autoGamma atoms (cleanForm atoms φ)) c t
              /
                (runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                  (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
                  (autoGamma atoms (cleanForm atoms φ))) ^ n
            ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (runCount
          (scaledAtoms atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
            (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
            (autoGamma atoms (cleanForm atoms φ)))
          (cleanForm atoms φ) ε δ hε0 hε1 hn (isPositive_cleanForm atoms φ)
          (scaledBdd atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
            (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
            (autoGamma atoms (cleanForm atoms φ)))
          (runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                (isPositive_cleanForm atoms φ)
                (cleanBdd atoms hφ hbdd hint) (autoGamma atoms (cleanForm atoms φ))
              * autoGamma atoms (cleanForm atoms φ))) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) =
        (inputParams atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)).thresh →
      Terminates
          (inputParams atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
            (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint))
          (runOracles
            (scaledAtoms atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
              (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
              (autoGamma atoms (cleanForm atoms φ)))
            (cleanForm atoms φ) ε δ hε0 hε1 hn (isPositive_cleanForm atoms φ)
            (scaledBdd atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
              (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
              (autoGamma atoms (cleanForm atoms φ)))
            (fun i =>
              runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                    (isPositive_cleanForm atoms φ)
                    (cleanBdd atoms hφ hbdd hint) (autoGamma atoms (cleanForm atoms φ))
                • autoCen atoms (cleanForm atoms φ) i)
            (runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                  (isPositive_cleanForm atoms φ)
                  (cleanBdd atoms hφ hbdd hint) (autoGamma atoms (cleanForm atoms φ))
                * autoGamma atoms (cleanForm atoms φ)) c t) (toDNFd (cleanForm atoms φ)) →
      runCost
          (inputParams atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
            (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint))
          (runOracles
            (scaledAtoms atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
              (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
              (autoGamma atoms (cleanForm atoms φ)))
            (cleanForm atoms φ) ε δ hε0 hε1 hn (isPositive_cleanForm atoms φ)
            (scaledBdd atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
              (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
              (autoGamma atoms (cleanForm atoms φ)))
            (fun i =>
              runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                    (isPositive_cleanForm atoms φ)
                    (cleanBdd atoms hφ hbdd hint) (autoGamma atoms (cleanForm atoms φ))
                • autoCen atoms (cleanForm atoms φ) i)
            (runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                  (isPositive_cleanForm atoms φ)
                  (cleanBdd atoms hφ hbdd hint) (autoGamma atoms (cleanForm atoms φ))
                * autoGamma atoms (cleanForm atoms φ)) c t)
          cVol cSample
          (runPrec
            (scaledAtoms atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
              (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
              (autoGamma atoms (cleanForm atoms φ)))
            (cleanForm atoms φ) ε δ hε0 hε1 hn (isPositive_cleanForm atoms φ)
            (scaledBdd atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
              (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint)
              (autoGamma atoms (cleanForm atoms φ)))
            (runScale atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
                  (isPositive_cleanForm atoms φ)
                  (cleanBdd atoms hφ hbdd hint) (autoGamma atoms (cleanForm atoms φ))
                * autoGamma atoms (cleanForm atoms φ))) (toDNFd (cleanForm atoms φ))
        ≤ (toDNFd (cleanForm atoms φ)).length * (cVol + cSample * thr)) :=
  ttc_volume_cleanInput atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hbdd hint

#print axioms ttc_volume_estimate

end Ttc
