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
`F = (atoms, φ)`, the accuracy `ε`, the confidence `δ`.  **Eleven binders**

```
atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos
```

and among them there is no interpretation, no parameter block, no converter, no
oracle, no precision, no inscribed-ball data — and no boundedness hypothesis.

The seven quantities the guarantee is *about* — `Ttc.ttcIndex`, `Ttc.ttcRates`,
`Ttc.ttcEstimate`, `Ttc.ttcThresh`, `Ttc.ttcTerminates`, `Ttc.ttcCost`,
`Ttc.ttcNumCubes` — are **defined in this file**, immediately below, so nothing the
headline names has to be chased out of `Model/`.  Each takes exactly the inputs
above and composes the run internally.  Each is a pure abbreviation carrying an
identifying `rfl` lemma (`Ttc.ttcEstimate_def` and friends), and the fact that this
theorem's proof is a bare application, with no rewriting, is the structural check
that they name what they claim to name.

## Definitional closure — what those seven bodies reach for

The seven definitions are *stated* here; their **bodies are not self-contained**.
Exactly as in the reference layout, the names live in `Model/` and the terms they
abbreviate live outside it, and this is the enumeration of everything outside
`Model/` that the statement's meaning therefore depends on.  **None of the
following is in `Model/`; all of it is the trusted base beyond `Model/`.**

* **The `Exec/Api` auxiliaries** the bodies name directly — `Ttc.ttcInput` (the
  preprocessed formula, `Ttc.cleanForm ∘ Ttc.pruneForm`), its two discharged
  obligations `Ttc.ttcInput_isPositive` and `Ttc.ttcInput_bdd`, the inscribed-ball
  and dilation data `Ttc.ttcRadius`, `Ttc.ttcScale`, `Ttc.ttcAtoms`,
  `Ttc.ttcAtoms_bdd`, `Ttc.ttcCen`, `Ttc.ttcScaledRadius`, the parameter block
  `Ttc.ttcBlock`, the precision `Ttc.ttcPrec`, and the oracle bundle
  `Ttc.ttcOracleBundle`.
* **Through those, the `Exec/Inputs` run wrappers** `Ttc.runCount`, `Ttc.runRates`,
  `Ttc.ttcRunOutput`, `Ttc.runOracles`, `Ttc.runPrec`, `Ttc.inputParams`, and the
  dilation `Ttc.runScale` / `Ttc.scaledAtoms` (`Exec/Rescaled`), the deduplicated
  cube list `Ttc.toDNFd` (`Exec/Dedup`) and the cost/termination predicates
  `Ttc.runCost` and `Ttc.Terminates` (`Runtime`).
* **The constructed oracle bundle** — `Ttc.coveredOracles` (`Exec/Endgoal`) over
  `Ttc.mcVol` (`Exec/VolDischarge`), which is the volume oracle
  `Ttc.VolumeAlgorithm.monteCarlo` (`Volume/MonteCarlo`).  So `Vol_ED` is a
  *constructed* Monte-Carlo estimator, not an assumed one.
* **The constructed sampler** — `Ttc.e2eSampD` (`Exec/EndToEnd`) and the KV97 /
  ball-walk development it is built from, together with the canonicalisation data
  `Ttc.canonRfac`/`Ttc.canonAm`/`Ttc.canonBv`/`Ttc.canonDm` (`Exec/Canonical`).
* **The parameter block** — `Ttc.ttcParams` (`Exec/Params`), which `Ttc.inputParams`
  instantiates at `δ₀ = 4δ/5`.
* **The run's probability space** — `Ttc.trajLaw` (`Coupling/Family`) for the sample
  coins and `Ttc.MonteCarlo.coins` (`Volume/MonteCarlo`) for the volume coins.

So the definitional closure of what is asserted is `Model/Prelude` +
`Model/ProblemSetting` + `Model/Pseudocode` + this file + the list above.  What is
*not* in it is every proof: `Exec/Prune`, `Exec/BddFromPos`, `Exec/Final` and the
whole probabilistic development are consumed only by `Ttc.ttc_volume_api`'s proof,
not by the statement.

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

## The two residual hypotheses

* `hφ` — negation-free.  Independent of boundedness in **both** directions
  (`Ttc.Independence.exists_isBounded_not_isPositive`,
  `Ttc.Independence.exists_isPositive_not_isBounded`), so neither can replace the other.
  Removable in principle at a bad price — see `Findings/OpenHalfspace.lean`.
* `hpos` — `0 < Vol(F)`.  Strictly weaker than the per-cube full-dimensionality it
  replaced: `Ttc.volSol_pos_of_interior` proves that implication, and
  `Ttc.hint_not_derivable` refutes the converse.

## `hbdd` is gone — **derived**, not dropped

The statement used to carry a twelfth binder,
`hbdd : Bornology.IsBounded (sol (atomSet atoms) φ)`.  What the chain actually needs is
boundedness of `Sol` of the **pruned** formula, and
`Ttc.isBounded_sol_pruneForm_of_volSol_pos` (`Exec/BddFromPos`) proves exactly that
from `hφ` and `hpos` alone: `hpos` bounds the volume of `Sol(F)` away from `⊤`, every
surviving cube's region is convex with a nonempty interior *by construction*, and a
convex set with an interior point and finite volume is bounded
(`Ttc.isBounded_of_convex_of_interior_of_volume_ne_top` — the step Mathlib does not
have).  The pruned `Sol` is the finite union of those regions.

That derivation became possible **only after the pruning round**.  Before it a cube of
the DNF can be a *line*: convex, unbounded, and of volume `0` — so it contributes
nothing to `Vol(F)` and `hpos` was perfectly consistent with an unbounded `Sol(F)`.
`Ttc.hint_not_derivable` (`Exec/Degenerate`) is the machine-checked witness that
`hpos` does not imply per-cube full-dimensionality, which is exactly the gap.
Pruning deletes those cubes, `Ttc.interior_nonempty_pruneForm` supplies the interior
point, and only then does "positive volume" imply "bounded".  Nothing here claims
`0 < Vol(F) → IsBounded (sol (atomSet atoms) φ)` at the **unpruned** formula; that
implication is false, and it is not needed.

Non-vacuity: `Ttc.TwoCube.ttc_volume_estimate_two_cube_full` (`Witness/FullTwoCube.lean`).
The audit is `AUDIT.md` §1e–§1g.

`sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ttc

open MeasureTheory Set

section Measured

variable {A : Type*} {n : ℕ}

/-! ## The seven quantities the guarantee is about

Each takes exactly the algorithm's inputs `atoms φ ε δ hε0 hε1 hn hφ hpos`, and each
is a pure abbreviation: a `def` with a closed body, plus a `rfl` lemma exhibiting that
body.  Nothing here asserts anything.  What the bodies reach for outside `Model/` is
enumerated in this module's docstring. -/

/-- **`|Sol(F) ∩ 𝕃ⁿ|` at the computed precision** — the index the run's sample coins
range over, so a sample trajectory has type `ℕ → Fin (ttcIndex …) → ℕ`. -/
noncomputable def ttcIndex (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : ℕ :=
  runCount (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) ε δ hε0 hε1 hn
    (ttcInput_isPositive atoms φ) (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos)

theorem ttcIndex_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos
      = runCount (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
          (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) := rfl

/-- **The level-`0` rate vector `θ`** (`alg:ttc` line 20) at the volume coins `c`:
the sampler's mass at each enumerated lattice point times that point's cube's volume
estimate.  `Ttc.trajLaw` of this is the law the sample coins are drawn from. -/
noncomputable def ttcRates (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n) : Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℝ :=
  runRates (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) ε δ hε0 hε1 hn
    (ttcInput_isPositive atoms φ) (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c

theorem ttcRates_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n) :
    ttcRates atoms φ ε δ hε0 hε1 hn hφ hpos c
      = runRates (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
          (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c := rfl

/-- **What `TTC(F, ε, δ)` returns on the run `(c, t)`, brought back to the original
scale** — `Ttc.ttcRunOutput` at the dilated input, divided by `ttcScaleⁿ`.

The division is part of the measured quantity: the run is performed on the dilated
body `c · Sol(F)`, whose volume is `cⁿ · Vol(Sol F)`, so this — and not the raw
output — is what the accuracy conjunct compares with `Ttc.volSol` of the original
body. -/
noncomputable def ttcEstimate (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) : ℝ :=
  ttcRunOutput (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) ε δ
      hε0 hε1 hn (ttcInput_isPositive atoms φ)
      (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
      (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
      (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t
    / (ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos) ^ n

theorem ttcEstimate_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) :
    ttcEstimate atoms φ ε δ hε0 hε1 hn hφ hpos c t
      = ttcRunOutput (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
            (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
            (isPositive_cleanForm atoms (pruneForm atoms φ))
            (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
            (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
            (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t
          / (ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos) ^ n := rfl

/-- **The sample threshold `Thresh`** of the computed parameter block — the quantity
the cost bound is linear in. -/
noncomputable def ttcThresh (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : ℝ :=
  (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos).thresh

theorem ttcThresh_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcThresh atoms φ ε δ hε0 hε1 hn hφ hpos
      = (inputParams atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (cleanBdd atoms (isPositive_pruneForm atoms φ)
            (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos)
            (pruneInt atoms hφ hpos))).thresh := rfl

/-- **The run's absorption loop exits at every cube** — `Ttc.Terminates` at the
computed parameter block, the run's own oracles and the preprocessed formula's cube
list.  This is the hypothesis `thm:runtime` needs and the paper leaves unstated. -/
def ttcTerminates (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) : Prop :=
  Terminates (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) (toDNFd (ttcInput atoms φ))

theorem ttcTerminates_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) :
    ttcTerminates atoms φ ε δ hε0 hε1 hn hφ hpos c t
      = Terminates (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t)
          (toDNFd (cleanForm atoms (pruneForm atoms φ))) := rfl

/-- **The charged cost of the run `(c, t)`** — `Ttc.runCost` at the computed
parameter block, the run's oracles, the per-call costs `cVol`/`cSample` and the
computed precision, folded over the preprocessed formula's cube list. -/
noncomputable def ttcCost (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ)
    (cVol cSample : ℕ) : ℕ :=
  runCost (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) cVol cSample
    (ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos) (toDNFd (ttcInput atoms φ))

theorem ttcCost_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ)
    (cVol cSample : ℕ) :
    ttcCost atoms φ ε δ hε0 hε1 hn hφ hpos c t cVol cSample
      = runCost (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) cVol cSample
          (ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos)
          (toDNFd (cleanForm atoms (pruneForm atoms φ))) := rfl

/-- **`m`, the number of cubes the run iterates over** — the length of the
preprocessed formula's DNF.  The cost bound is `m · (C_vol + C_sample · Thresh)`. -/
noncomputable def ttcNumCubes (atoms : A → LinAtom n) (φ : BForm A) : ℕ :=
  (toDNFd (ttcInput atoms φ)).length

theorem ttcNumCubes_def (atoms : A → LinAtom n) (φ : BForm A) :
    ttcNumCubes atoms φ = (toDNFd (cleanForm atoms (pruneForm atoms φ))).length := rfl

/-! ## The bridge to `Model/Pseudocode`

`Ttc.ttcEstimate` is `Model/Pseudocode`'s own `Ttc.ttcOutput`, divided by `qⁿ`.
Together with `Ttc.ttcInput_eq_preprocess` (`Exec/Api`) this puts both the algorithm
that is certified and the input it is certified on inside the audit path
`Model/Prelude → Model/ProblemSetting → Model/Pseudocode → Model/Theorem`. -/

/-- **The measured quantity is `Model/Pseudocode`'s `Ttc.ttcOutput`, divided by `qⁿ`** —
lines A12–A13 of the preprocessing transcription, by `rfl`. -/
theorem ttcEstimate_eq_ttcOutput (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) :
    ttcEstimate atoms φ ε δ hε0 hε1 hn hφ hpos c t
      = ttcOutput (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c) toDNFd
          (ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) t
        / (ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos) ^ n := rfl

end Measured

/-! ## The headline -/

/-- **`thm:volumettc` + `thm:runtime`.**  `TTC` is run on `F = (atoms, φ)` at accuracy
`ε` and confidence `δ`.

* **Accuracy.**  `Pr[ output ∈ (1 ± ε)·Vol(F) ] ≥ 1 − δ`, over the volume coins (law
  `Ttc.MonteCarlo.coins n`) and the sample coins (law `Ttc.trajLaw`).  The output is
  `Ttc.ttcEstimate` and the target is the **user's own** `Vol(F)`.
* **Running time.**  On every run, `alg:ttc`'s charged cost — one `Vol_ED` call plus one
  `GenerateSamples` draw per returned point — is at most
  `m · (C_vol + C_sample · Thresh)`, under `Ttc.ttcTerminates`.

Eleven binders, all conditions on the input, and only two of them shape hypotheses:
`hφ` and `hpos`.  See this module's docstring for the three preprocessing steps this
certifies `alg:ttc` *plus*, for what is known about `hφ` and `hpos`, for why the
former `hbdd` binder is now derived rather than assumed, and for the definitional
closure of the seven quantities named below.  Correctness, not efficiency: both
oracle routes are exponential in `n`. -/
theorem ttc_volume_estimate {A : Type*} {n : ℕ}
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    -- (accuracy) the output is within `(1 ± ε)·Vol(F)` with probability `≥ 1 − δ`
    (1 - δ ≤
      (∫⁻ c, trajLaw (ttcRates atoms φ ε δ hε0 hε1 hn hφ hpos c)
          {t | ttcEstimate atoms φ ε δ hε0 hε1 hn hφ hpos c t
                ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    -- (running time) `alg:ttc`'s charged cost, on every run, under `Ttc.ttcTerminates`
    (∀ (c : ℕ → Space n) (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = ttcThresh atoms φ ε δ hε0 hε1 hn hφ hpos →
      ttcTerminates atoms φ ε δ hε0 hε1 hn hφ hpos c t →
      ttcCost atoms φ ε δ hε0 hε1 hn hφ hpos c t cVol cSample
        ≤ ttcNumCubes atoms φ * (cVol + cSample * thr)) :=
  ttc_volume_api atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos

#print axioms ttc_volume_estimate

end Ttc
