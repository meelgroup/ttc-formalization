/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Api

/-!
# `Model/Run`: the quantities the headline names

The **fifth file of `Model/`**, and the one that makes the other two properties of
the audit surface hold at once:

* `Model/Theorem.lean` contains **one declaration** — `Ttc.ttc_volume_estimate` —
  and no `def`, no auxiliary lemma, no proof to work through; and
* the headline's *type* names **only `Model/` definitions** — the sole exception
  being the run's probability space, `Ttc.MonteCarlo.coins` and `Ttc.trajLaw`.

`Ttc.ttcTerminates`, `Ttc.ttcCost`, `Ttc.ttcNumCubes` and `Ttc.ttcThresh` below
are what buys the runtime conjunct that exception-free surface: they are the
folded names for `Ttc.Terminates`, `Ttc.runCost`, the cube count and
`Params.thresh` of `Runtime.lean`, each unfolding to its target by `rfl`.

Those two cannot both hold with the named quantities sitting in `Exec/Api.lean`,
and they cannot sit in `Model/Pseudocode.lean` either: `Exec/Api` imports it, and
their bodies name theorems from the whole downstream development.  So they live
here — *downstream* of `Ttc.Exec.Api`, *upstream* of `Ttc.Model.Theorem`.

## What is here

The seven quantities the guarantee is about —

```
ttcIndex  ttcRates  ttcEstimate  ttcThresh  ttcTerminates  ttcCost  ttcNumCubes
```

— together with the five auxiliaries the headline's statement also names:
`Ttc.ttcInput` (the preprocessed formula the run is on), `Ttc.ttcScale` (the
dilation), `Ttc.ttcBlock` (the parameter block), `Ttc.ttcPrec` (`GetPrecision`'s
`ρ`) and `Ttc.ttcOracleBundle` (the oracle bundle the run reads).

## Nothing here is an assumption

**Every `def` in this file is a pure abbreviation and asserts nothing.**  Each is
a `def` with a closed body, and each carries an identifying `rfl` lemma
(`Ttc.ttcInput_def`, `Ttc.ttcScale_def`, `Ttc.ttcIndex_def`, …) spelling that body
out.  No name here stands in for a proof: what a name means is exhibited,
machine-checked, next to the name.  The structural check that these are the
*right* abbreviations is that `Ttc.ttc_volume_estimate`'s proof is the bare
application `Ttc.ttc_volume_api atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos`, with no
rewriting — a wrong abbreviation is a build error, not a silent divergence.

## The bodies still reach into `Exec/`

This file buys the headline its `Model/`-only *surface*; it does not pretend the
*closure* is inside `Model/`.  The bodies below are built from `Ttc.ttcAtoms`,
`Ttc.ttcCen`, `Ttc.ttcScaledRadius`, `Ttc.ttcRadius`, `Ttc.ttcInput_isPositive`
and `Ttc.ttcAtoms_bdd` (`Exec/Api`), and through them from `Ttc.pruneForm`,
`Ttc.cleanForm`, `Ttc.autoGamma`, `Ttc.autoCen`, `Ttc.runScale`,
`Ttc.scaledAtoms`, `Ttc.inputParams`, `Ttc.runPrec`, `Ttc.runCount`,
`Ttc.runRates`, `Ttc.runOracles` and `Ttc.ttcRunOutput`.  **That definitional
closure is `AUDIT.md` §1h**, which is written to be read alongside
`Model/Theorem.lean`; an auditor who wants to know what the headline's names
unfold to reads it there, and the `_def` lemmas below are the first step of that
unfolding.

## Shared inputs

Each declaration takes exactly the algorithm's inputs

```
atoms φ ε δ hε0 hε1 hn hφ hpos
```

written once as the `variable` block below; Lean re-adds them, in that order, to
each declaration that mentions them.  `Ttc.ttcInput` and `Ttc.ttcNumCubes` mention
only `atoms` and `φ`, so they take only those two.  `#check @Ttc.ttcEstimate` and
friends print the argument lists in full.
-/

namespace Ttc

open MeasureTheory Set Pointwise

section Run

variable {A : Type*} {n : ℕ}

/-! ## The formula the algorithm is handed -/

/-- **The formula `TTC` is actually run on** — the user's `φ` with its degenerate
cubes pruned (`Ttc.pruneForm`) and its zero-normal atoms cleaned (`Ttc.cleanForm`).
`Ttc.volSol` is unchanged by both passes, so the accuracy target stays the original
`Vol(F)`. -/
noncomputable def ttcInput (atoms : A → LinAtom n) (φ : BForm A) : BForm A :=
  cleanForm atoms (pruneForm atoms φ)

theorem ttcInput_def (atoms : A → LinAtom n) (φ : BForm A) :
    ttcInput atoms φ = cleanForm atoms (pruneForm atoms φ) := rfl

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)

/-! ## The dilation, the parameter block and the precision -/

/-- **The dilation `TTC` applies to its input** — `Ttc.runScale` at the preprocessed
formula and the inscribed radius `Ttc.ttcRadius`.  `≥ 1` always
(`Ttc.runScale_pos`).  The headline divides the run's output by `ttcScale ^ n`,
which is lines A12–A13 of the preprocessing taken back out. -/
noncomputable def ttcScale : ℝ :=
  runScale atoms (ttcInput atoms φ) ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
    (ttcInput_bdd atoms φ hφ hpos) (ttcRadius atoms φ)

theorem ttcScale_def :
    ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos
      = runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (cleanBdd atoms (isPositive_pruneForm atoms φ)
            (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos) (pruneInt atoms hφ hpos))
          (autoGamma atoms (cleanForm atoms (pruneForm atoms φ))) := rfl

/-- **The parameter block `TTC` computes** (`alg:ttc` lines 17–20) — `Ttc.inputParams`
at the preprocessed formula.  Note it is at the *original* `atoms`: the dilation does
not move the parameter block (`Ttc.inputParams_scaleAtoms`). -/
noncomputable def ttcBlock : Params :=
  inputParams atoms (ttcInput atoms φ) ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
    (ttcInput_bdd atoms φ hφ hpos)

theorem ttcBlock_def :
    ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos
      = inputParams atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (cleanBdd atoms (isPositive_pruneForm atoms φ)
            (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos)
            (pruneInt atoms hφ hpos)) := rfl

/-- **`GetPrecision`'s output `ρ`** (`alg:ttc` line 17), at the dilated input. -/
noncomputable def ttcPrec : ℤ :=
  runPrec (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) ε δ hε0 hε1 hn
    (ttcInput_isPositive atoms φ) (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos)

theorem ttcPrec_def :
    ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos
      = runPrec (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
          (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) := rfl

/-! ## The seven quantities the guarantee is about -/

/-- **`|Sol(F) ∩ 𝕃ⁿ|` at the computed precision** — the sample coins' index. -/
noncomputable def ttcIndex : ℕ :=
  runCount (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) ε δ hε0 hε1 hn
    (ttcInput_isPositive atoms φ) (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos)

theorem ttcIndex_def :
    ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos
      = runCount (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
          (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) := rfl

/-- **The oracle bundle `alg:ttc` reads on the run `(c, t)`** — `Vol_ED` is
`Ttc.mcVol` at the volume coins `c`, the covered-lattice sampler is at the sample
coins `t`, which are indexed by `Ttc.ttcIndex`.  Nothing here is a hypothesis; it
is a closed term. -/
noncomputable def ttcOracleBundle (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) : Oracles n (Cube A) :=
  runOracles (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) ε δ hε0 hε1 hn
    (ttcInput_isPositive atoms φ) (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t

theorem ttcOracleBundle_def (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) :
    ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t
      = runOracles (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
          (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t := rfl

/-- **The level-`0` rate vector `θ`** (`alg:ttc` line 20); `Ttc.trajLaw` of it is the
law the sample coins are drawn from (`AUDIT.md` §1h). -/
noncomputable def ttcRates (c : ℕ → Space n) :
    Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℝ :=
  runRates (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) ε δ hε0 hε1 hn
    (ttcInput_isPositive atoms φ) (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c

theorem ttcRates_def (c : ℕ → Space n) :
    ttcRates atoms φ ε δ hε0 hε1 hn hφ hpos c
      = runRates (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
          (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c := rfl

/-- **What `TTC(F, ε, δ)` returns on `(c, t)`, brought back to the original scale** —
`Ttc.ttcRunOutput` at the dilated input, divided by `ttcScaleⁿ` (`AUDIT.md` §1h). -/
noncomputable def ttcEstimate (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) : ℝ :=
  ttcRunOutput (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) ε δ
      hε0 hε1 hn (ttcInput_isPositive atoms φ)
      (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
      (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
      (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t
    / (ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos) ^ n

theorem ttcEstimate_def (c : ℕ → Space n)
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
noncomputable def ttcThresh : ℝ :=
  (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos).thresh

theorem ttcThresh_def :
    ttcThresh atoms φ ε δ hε0 hε1 hn hφ hpos
      = (inputParams atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (cleanBdd atoms (isPositive_pruneForm atoms φ)
            (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos)
            (pruneInt atoms hφ hpos))).thresh := rfl

/-- **The run's absorption loop exits at every cube** — `Ttc.Terminates`; the
hypothesis `thm:runtime` needs and the paper leaves unstated (`AUDIT.md` §1h). -/
def ttcTerminates (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) : Prop :=
  Terminates (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) (toDNFd (ttcInput atoms φ))

theorem ttcTerminates_def (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) :
    ttcTerminates atoms φ ε δ hε0 hε1 hn hφ hpos c t
      = Terminates (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t)
          (toDNFd (cleanForm atoms (pruneForm atoms φ))) := rfl

/-- **The charged cost of the run `(c, t)`** — `Ttc.runCost` folded over the
preprocessed formula's cube list (`AUDIT.md` §1h). -/
noncomputable def ttcCost (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ)
    (cVol cSample : ℕ) : ℕ :=
  runCost (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) cVol cSample
    (ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos) (toDNFd (ttcInput atoms φ))

theorem ttcCost_def (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ)
    (cVol cSample : ℕ) :
    ttcCost atoms φ ε δ hε0 hε1 hn hφ hpos c t cVol cSample
      = runCost (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) cVol cSample
          (ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos)
          (toDNFd (cleanForm atoms (pruneForm atoms φ))) := rfl

/-- **`m`, the number of cubes the run iterates over.** -/
noncomputable def ttcNumCubes : ℕ :=
  (toDNFd (ttcInput atoms φ)).length

theorem ttcNumCubes_def :
    ttcNumCubes atoms φ = (toDNFd (cleanForm atoms (pruneForm atoms φ))).length := rfl

/-! ## The two bridges to `Model/Pseudocode` -/

/-- **The measured quantity is `Model/Pseudocode`'s `Ttc.ttcOutput`, divided by `qⁿ`** —
lines A12–A13 of the preprocessing transcription, by `rfl`.  `Model/Theorem.lean`'s
accuracy conjunct is stated with the right-hand side, so this lemma is also the
statement of what that conjunct measures. -/
theorem ttcEstimate_eq_ttcOutput (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) :
    ttcEstimate atoms φ ε δ hε0 hε1 hn hφ hpos c t
      = ttcOutput (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c) toDNFd
          (ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) t
        / (ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos) ^ n := rfl

/-- **The input the run is on is `Model/Pseudocode`'s `Ttc.preprocess`**, by `rfl`. -/
theorem ttcInput_eq_preprocess :
    ttcInput atoms φ = preprocess atoms φ := rfl

end Run

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ttcInput_def
#print axioms Ttc.ttcScale_def
#print axioms Ttc.ttcBlock_def
#print axioms Ttc.ttcPrec_def
#print axioms Ttc.ttcIndex_def
#print axioms Ttc.ttcOracleBundle_def
#print axioms Ttc.ttcRates_def
#print axioms Ttc.ttcEstimate_def
#print axioms Ttc.ttcThresh_def
#print axioms Ttc.ttcTerminates_def
#print axioms Ttc.ttcCost_def
#print axioms Ttc.ttcNumCubes_def
#print axioms Ttc.ttcEstimate_eq_ttcOutput
#print axioms Ttc.ttcInput_eq_preprocess
