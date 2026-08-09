/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Api

/-!
# The main theorem: `thm:volumettc` + `thm:runtime` for `TTC(F, ε, δ)`

The **statement layer**: one theorem, and no proof to work through — it is one
application of `Ttc.ttc_volume_api` (`Exec/Api`).

Audit path — `Model/`, then stop: `Model/Prelude` (the vocabulary),
`Model/ProblemSetting` (what `Vol(F)` is and what `(1 ± ε)` means),
`Model/Pseudocode` (`alg:ttc`, transcribed line by line), this file.

`TTC` takes three inputs, so three inputs is what this statement takes: the formula
`F = (atoms, φ)`, the accuracy `ε`, the confidence `δ`.  **Twelve binders**, and among
them there is no interpretation, no parameter block, no converter, no oracle, no
precision and no inscribed-ball data.

The four quantities the guarantee is *about* — `Ttc.ttcRates`, `Ttc.ttcEstimate`,
`Ttc.ttcCost`, `Ttc.ttcNumCubes` (`Exec/Api`) — each take exactly these inputs and
compose the run internally.  Each is a pure abbreviation carrying an identifying `rfl`
lemma (`Ttc.ttcEstimate_def` and friends), and the fact that this theorem's proof is a
bare application, with no rewriting, is the structural check that they name what they
claim to name.

## What is certified is `alg:ttc` plus three preprocessing steps

Read this before quoting the statement.  Two of the three change what the algorithm
*does*; only one is cosmetic.

* **A dilation** (`Exec/Rescaled`).  `alg:ttc` sets `p ← 1` and only halves it, so its
  sketch is `Poisson(Λ)` with `Λ ≤ Vol(Sol F)`; on a body of volume `10⁻⁶` it draws
  `Pois(10⁻⁶)` points and returns `0`.  **The printed algorithm is wrong there**, not
  merely unproved (`Ttc.Box.big_not_derivable`, README finding 20).  So the input is
  dilated by `Ttc.runScale` and the estimate divided by `cⁿ`.
* **A pruning** (`Exec/Prune`).  Degenerate (lower-dimensional) cubes are dropped.  This
  changes `Sol(F)` by a null set — `Ttc.sol_pruneForm_subset` is a genuine `⊆`, strict on
  `Ttc.degForm` — and is sound *only* because the conclusion merely measures `sol`
  (`Ttc.volSol_pruneForm`).
* **A cleanup** (`Exec/Cleanup`).  Zero-normal atoms are constant-folded.  Benign:
  `Ttc.sol_cleanForm` is an exact set equality.

The inscribed ball is *constructed* (`Ttc.autoCen`, `Ttc.autoGamma`), but it is **not**
`alg:prec` line 86's LP — it is *some* inscribed ball, and non-maximality only inflates
`ρ = ⌈log₁₀(γ/γ̂)⌉`, so the guarantee is unaffected and only the precision is looser.

## The three residual hypotheses

* `hφ` — negation-free.  Independent of `hbdd` in **both** directions
  (`Ttc.Independence.exists_isBounded_not_isPositive`,
  `Ttc.Independence.exists_isPositive_not_isBounded`), so neither can replace the other.
  Removable in principle at a bad price — see `Findings/OpenHalfspace.lean`.
* `hbdd` — bounded solution set.  *Necessary*: `Ttc.volSol` is an `ENNReal.toReal` and
  `toReal ⊤ = 0`, so an unbounded `Sol(F)` would certify "the output is ≈ 0" (finding 16).
* `hpos` — `0 < Vol(F)`.  Strictly weaker than the per-cube full-dimensionality it
  replaced: `Ttc.volSol_pos_of_interior` proves that implication, and
  `Ttc.hint_not_derivable` refutes the converse.

Non-vacuity: `Ttc.TwoCube.ttc_volume_estimate_two_cube_full` (`Witness/FullTwoCube.lean`).
The audit is `AUDIT.md` §1e–§1g.

`sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ttc

open MeasureTheory Set

/-- **`thm:volumettc` + `thm:runtime`.**  `TTC` is run on `F = (atoms, φ)` at accuracy
`ε` and confidence `δ`.

* **Accuracy.**  `Pr[ output ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, over the volume coins (law
  `Ttc.MonteCarlo.coins n`) and the sample coins (law `Ttc.trajLaw`).  The output is
  `Ttc.ttcEstimate` and the target is the **user's own** `Vol(F)`.
* **Running time.**  On every run, `alg:ttc`'s charged cost — one `Vol_ED` call plus one
  `GenerateSamples` draw per returned point — is at most
  `m · (C_vol + C_sample · Thresh)`, under `Ttc.ttcTerminates`.

Twelve binders, all conditions on the input.  See this module's docstring for the three
preprocessing steps this certifies `alg:ttc` *plus*, and for what is known about each of
`hφ`, `hbdd`, `hpos`.  Correctness, not efficiency: both oracle routes are exponential
in `n`. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- (accuracy) the output is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      (∫⁻ c, trajLaw (ttcRates atoms φ ε δ hε0 hε1 hn hφ hbdd hpos c)
          {t | ttcEstimate atoms φ ε δ hε0 hε1 hn hφ hbdd hpos c t
                ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    -- (running time) `alg:ttc`'s charged cost, on every run, under `Ttc.ttcTerminates`
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hbdd hpos) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = ttcThresh atoms φ ε δ hε0 hε1 hn hφ hbdd hpos →
      ttcTerminates atoms φ ε δ hε0 hε1 hn hφ hbdd hpos c t →
      ttcCost atoms φ ε δ hε0 hε1 hn hφ hbdd hpos c t cVol cSample
        ≤ ttcNumCubes atoms φ * (cVol + cSample * thr)) :=
  ttc_volume_api atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hbdd hpos

#print axioms ttc_volume_estimate

end Ttc
