/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.BddFromPos

/-!
# `Exec/Api`: the statement API — the quantities the headline is *about*

`Ttc.ttc_volume_prune` (`Exec/Prune`) is the theorem this module re-expresses.  Its
conclusion is correct but unreadable: every wrapper is applied to another wrapper's
*full* argument list, so a single sub-term such as "the run's rate vector" spans a
dozen lines and repeats `cleanForm atoms (pruneForm atoms φ)` eight times.

This module names the sub-terms.  Each definition below takes **exactly the
algorithm's inputs** —

```
atoms φ ε δ hε0 hε1 hn hφ hpos
```

— and composes `Ttc.pruneForm`, `Ttc.cleanForm`, `Ttc.autoGamma`, `Ttc.autoCen`,
`Ttc.runScale`, `Ttc.scaledAtoms` and `Ttc.inputParams` internally.  Its proof is
one application of `Ttc.ttc_volume_prune`.

**The seven quantities the headline is *about* are not here.**  `Ttc.ttcIndex`,
`Ttc.ttcRates`, `Ttc.ttcEstimate`, `Ttc.ttcThresh`, `Ttc.ttcTerminates`,
`Ttc.ttcCost` and `Ttc.ttcNumCubes` are defined in `Model/Theorem.lean`, so that
every quantity `Ttc.ttc_volume_estimate` names is defined inside `Model/`.  What
stays here is the *auxiliary* layer their bodies are built from — the
preprocessed input, the inscribed-ball data, the dilation, the parameter block,
the precision and the oracle bundle.  `Ttc.ttc_volume_api` below therefore states
the guarantee with those seven bodies written out; `Model/Theorem.lean` states it
with the seven names, and the two statements are definitionally the same term,
which is exactly why `Ttc.ttc_volume_estimate`'s proof is the bare application
`ttc_volume_api atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos`.

## What the algorithm is actually handed

Two preprocessing passes stand between the user's formula and the run, and
`Ttc.ttcInput` is their composite:

```
ttcInput atoms φ = cleanForm atoms (pruneForm atoms φ)
```

* `Ttc.pruneForm` **prunes the degenerate cubes** — those whose region has empty
  interior (lower-dimensional or void).  They are null sets, so deleting them does
  not change `Ttc.volSol`, and it *makes true* the full-dimensionality condition the
  sampler needs (`Ttc.pruneInt`), which is not derivable otherwise
  (`Ttc.hint_not_derivable`).
* `Ttc.cleanForm` **cleans the zero-normal atoms** — literals `0 · x ≤ b` denote
  `Set.univ` or `∅`, so they are deleted along with the cubes they void.  This
  changes no solution set at all (`Ttc.sol_cleanForm` is an equality of sets) and
  makes true the nondegenerate-facet condition.

**The accuracy target is the original `Vol(F)`.**  Every occurrence of the formula
in `Ttc.ttc_volume_api`'s conclusion is at `Ttc.ttcInput atoms φ` — that is what the
algorithm runs on — *except* the accuracy conjunct, which compares the estimate with
`volSol (atomSet atoms) φ` at the user's own `φ`.  Nothing post-processes the
estimate to make that work: `Ttc.volSol_pruneForm` and `Ttc.volSol_cleanForm` say
the two volumes are equal.

## Nothing here is an assumption

**Every `def` in this file is a pure abbreviation and asserts nothing.**  Each is a
`def` whose body is a closed term, and each carries an identifying `rfl` lemma
(`Ttc.ttcInput_def`, `Ttc.ttcScale_def`, `Ttc.ttcBlock_def`, …) spelling out that
body, proved by `rfl`.  So no name in this file stands in for a proof: what a name
means is exhibited, machine-checked, next to the name.

The single structural check that these are the *right* abbreviations is
`Ttc.ttc_volume_api` itself.  Its proof is the single application

```
ttc_volume_prune atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ
  (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos) hpos
```

with no rewriting, no `show`, and no conversion: it typechecks exactly when every
definition here is **definitionally** the sub-term of `ttc_volume_prune` it claims
to name.  A wrong abbreviation is a build error, not a silent divergence.

## Where `hbdd` went

`Ttc.ttc_volume_prune` asks for boundedness of `Sol` of the **pruned** formula, and
`Ttc.isBounded_sol_pruneForm_of_volSol_pos` (`Exec/BddFromPos`) proves exactly that
from `hφ` and `hpos` alone.  So the boundedness binder the chain used to carry is
gone — *derived*, not assumed — and that is the sole reason this module imports
`Exec/BddFromPos` rather than `Exec/Prune`.  The derivation is available only after
the pruning round: before it, a cube may be a *line* — convex, unbounded, of volume
`0` — so `hpos` was consistent with an unbounded `Sol(F)`.

## What each name is

* `Ttc.ttcInput` — the preprocessed formula the run is on, as above.
* `Ttc.ttcRadius` / `Ttc.ttcScale` / `Ttc.ttcAtoms` / `Ttc.ttcCen` — the
  `GetPrecision` inscribed-ball data for that formula, the dilation applied to it,
  and the dilated input.  `Ttc.ttcScaledRadius = ttcScale * ttcRadius` is the
  inscribed radius *after* the dilation, which is the `γ̂` every run wrapper takes.
* `Ttc.ttcBlock` / `Ttc.ttcPrec` — the parameter block `TTC` computes
  (`Ttc.inputParams`, hence `Ttc.ttcParams`) and the precision `ρ`.
* `Ttc.ttcOracleBundle` — the oracle bundle the run reads: `Ttc.mcVol` at the
  volume coins `c` and `Ttc.coveredOracles` at the sample coins `t`.

and the three obligations these discharge from the headline's own binders,
`Ttc.ttcInput_isPositive`, `Ttc.ttcInput_bdd`, `Ttc.ttcAtoms_bdd`.

The measured quantities built out of them — `Ttc.ttcIndex`, `Ttc.ttcRates`,
`Ttc.ttcEstimate`, `Ttc.ttcThresh`, `Ttc.ttcTerminates`, `Ttc.ttcCost`,
`Ttc.ttcNumCubes` — are in `Model/Theorem.lean`.
-/

namespace Ttc

open MeasureTheory Set Pointwise

section Api

variable {A : Type*} {n : ℕ}

/-! ## The formula the algorithm is handed

`Ttc.pruneForm` then `Ttc.cleanForm`, with the two obligations the run wrappers ask
of it discharged from the headline's own binders. -/

/-- **The formula `TTC` is actually run on** — the user's `φ` with its degenerate
cubes pruned (`Ttc.pruneForm`) and its zero-normal atoms cleaned (`Ttc.cleanForm`).
`Ttc.volSol` is unchanged by both passes, so the accuracy target stays the original
`Vol(F)`. -/
noncomputable def ttcInput (atoms : A → LinAtom n) (φ : BForm A) : BForm A :=
  cleanForm atoms (pruneForm atoms φ)

theorem ttcInput_def (atoms : A → LinAtom n) (φ : BForm A) :
    ttcInput atoms φ = cleanForm atoms (pruneForm atoms φ) := rfl

/-- The preprocessed formula is positive — unconditionally, both passes rebuilding
the formula from `Ttc.dnfForm`. -/
theorem ttcInput_isPositive (atoms : A → LinAtom n) (φ : BForm A) :
    (ttcInput atoms φ).IsPositive :=
  isPositive_cleanForm atoms (pruneForm atoms φ)

/-- `Sol` of the preprocessed formula is bounded — `Ttc.cleanBdd` over
`Ttc.isBounded_sol_pruneForm_of_volSol_pos`/`Ttc.pruneInt`, so `hφ` and `hpos` are
all that is spent.  No boundedness hypothesis: it is *derived* from `hpos` at the
pruned formula (`Exec/BddFromPos`). -/
theorem ttcInput_bdd (atoms : A → LinAtom n) (φ : BForm A) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    Bornology.IsBounded (sol (atomSet atoms) (ttcInput atoms φ)) :=
  cleanBdd atoms (isPositive_pruneForm atoms φ)
    (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos) (pruneInt atoms hφ hpos)

/-! ## The inscribed-ball data and the dilation

Four abbreviations for the terms `Exec/Rescaled`'s wrappers are applied to inside
`Ttc.ttc_volume_prune`.  All four are at `Ttc.ttcInput atoms φ`. -/

/-- **The inscribed radius `GetPrecision` computes** for the preprocessed formula:
`Ttc.autoGamma` at `Ttc.ttcInput atoms φ`. -/
noncomputable def ttcRadius (atoms : A → LinAtom n) (φ : BForm A) : ℝ :=
  autoGamma atoms (ttcInput atoms φ)

theorem ttcRadius_def (atoms : A → LinAtom n) (φ : BForm A) :
    ttcRadius atoms φ = autoGamma atoms (cleanForm atoms (pruneForm atoms φ)) := rfl

/-- **The dilation `TTC` applies to its input** — `Ttc.runScale` at the preprocessed
formula and the radius above.  `≥ 1` always (`Ttc.runScale_pos`). -/
noncomputable def ttcScale (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : ℝ :=
  runScale atoms (ttcInput atoms φ) ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
    (ttcInput_bdd atoms φ hφ hpos) (ttcRadius atoms φ)

theorem ttcScale_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos
      = runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (cleanBdd atoms (isPositive_pruneForm atoms φ)
            (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos) (pruneInt atoms hφ hpos))
          (autoGamma atoms (cleanForm atoms (pruneForm atoms φ))) := rfl

/-- **The dilated input** — the preprocessed formula's atoms with their bounds
scaled by `Ttc.ttcScale`.  This is the `A → LinAtom n` the run wrappers are applied
to. -/
noncomputable def ttcAtoms (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : A → LinAtom n :=
  scaledAtoms atoms (ttcInput atoms φ) ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
    (ttcInput_bdd atoms φ hφ hpos) (ttcRadius atoms φ)

theorem ttcAtoms_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos
      = scaledAtoms atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (cleanBdd atoms (isPositive_pruneForm atoms φ)
            (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos) (pruneInt atoms hφ hpos))
          (autoGamma atoms (cleanForm atoms (pruneForm atoms φ))) := rfl

/-- `Sol` of the dilated input is bounded — `Ttc.scaledBdd`, restated at
`Ttc.ttcAtoms` so that the run wrappers below can be applied to it. -/
theorem ttcAtoms_bdd (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    Bornology.IsBounded
      (sol (atomSet (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)) (ttcInput atoms φ)) :=
  scaledBdd atoms (ttcInput atoms φ) ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
    (ttcInput_bdd atoms φ hφ hpos) (ttcRadius atoms φ)

/-- **The dilated centres** — `Ttc.autoCen` at the preprocessed formula, moved by
the dilation, so that each dilated cube's inscribed ball is centred correctly. -/
noncomputable def ttcCen (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    {c : Cube A // c ∈ toDNFd (ttcInput atoms φ)} → Space n :=
  fun i => ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos • autoCen atoms (ttcInput atoms φ) i

theorem ttcCen_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos
      = fun i => ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos
          • autoCen atoms (cleanForm atoms (pruneForm atoms φ)) i := rfl

/-- **The inscribed radius after the dilation**, `ttcScale * ttcRadius` — the `γ̂`
every run wrapper of `Exec/Inputs` is applied to. -/
noncomputable def ttcScaledRadius (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : ℝ :=
  ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos * ttcRadius atoms φ

theorem ttcScaledRadius_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos
      = ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos
          * autoGamma atoms (cleanForm atoms (pruneForm atoms φ)) := rfl

/-! ## The parameter block and the precision -/

/-- **The parameter block `TTC` computes** (`alg:ttc` lines 17–20) — `Ttc.inputParams`
at the preprocessed formula.  Note it is at the *original* `atoms`: the dilation does
not move the parameter block (`Ttc.inputParams_scaleAtoms`). -/
noncomputable def ttcBlock (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : Params :=
  inputParams atoms (ttcInput atoms φ) ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
    (ttcInput_bdd atoms φ hφ hpos)

theorem ttcBlock_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos
      = inputParams atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (cleanBdd atoms (isPositive_pruneForm atoms φ)
            (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos) (pruneInt atoms hφ hpos)) := rfl

/-- **`GetPrecision`'s output `ρ`** (`alg:ttc` line 17), at the dilated input. -/
noncomputable def ttcPrec (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : ℤ :=
  runPrec (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) ε δ hε0 hε1 hn
    (ttcInput_isPositive atoms φ) (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos)

theorem ttcPrec_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos
      = runPrec (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
          (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) := rfl

/-! ## The oracle bundle

The last auxiliary.  Its sample-coin argument is indexed by `|Sol(F) ∩ 𝕃ⁿ|` at the
computed precision — the quantity `Model/Theorem.lean` names `Ttc.ttcIndex`, written
out here since the name is not in scope. -/

/-- **The oracle bundle `alg:ttc` reads on the run `(c, t)`** — `Vol_ED` is
`Ttc.mcVol` at the volume coins `c`, the covered-lattice sampler is at the sample
coins `t`.  Nothing here is a hypothesis; it is a closed term. -/
noncomputable def ttcOracleBundle (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n)
    (t : ℕ → Fin (runCount (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ)
          ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
          (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos)) → ℕ) : Oracles n (Cube A) :=
  runOracles (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) ε δ hε0 hε1 hn
    (ttcInput_isPositive atoms φ) (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
    (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t

theorem ttcOracleBundle_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)
    (c : ℕ → Space n)
    (t : ℕ → Fin (runCount (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ)
          ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
          (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos)) → ℕ) :
    ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t
      = runOracles (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
          (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
          (isPositive_cleanForm atoms (pruneForm atoms φ))
          (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t := rfl

/-! ## The headline, restated

Same theorem as `Ttc.ttc_volume_prune`, same conclusion — only spelled with the
names above, and with the pruned-boundedness argument supplied rather than assumed,
so this statement has **eleven** binders.  The proof is the single application; it
typechecks exactly when every definition of this module is definitionally the
sub-term it names.

The seven measured quantities are written out here rather than named, because
their names — `Ttc.ttcIndex`, `Ttc.ttcRates`, `Ttc.ttcEstimate`, `Ttc.ttcThresh`,
`Ttc.ttcTerminates`, `Ttc.ttcCost`, `Ttc.ttcNumCubes` — are introduced downstream,
in `Model/Theorem.lean`.  Each conjunct below is *literally* the body of the
corresponding definition there, so `Ttc.ttc_volume_estimate` is this theorem
applied, with no rewriting. -/

/-- **`thm:volumettc` + `thm:runtime`, in the statement API.**  `TTC(F, ε, δ)` run
on `φ` — with the two preprocessing passes (`Ttc.pruneForm`, `Ttc.cleanForm`), the
inscribed-ball construction (`Ttc.autoCen`/`Ttc.autoGamma`), the dilation
(`Ttc.runScale`) and the parameter block (`Ttc.inputParams`) all internal to the
names.

* **Accuracy.**  `Pr[ ttcEstimate ∈ (1 ± ε)·Vol(Sol φ) ] ≥ 1 − δ`, over the joint
  law of the volume coins `Ttc.MonteCarlo.coins` and the sample trajectory
  `Ttc.trajLaw (ttcRates … c)`.  The target is the volume of the **original** body:
  neither preprocessing pass moves it.

* **Running time.**  On every run `(c, t)` whose absorption loops exit, the charged
  cost is at most `m · (C_vol + C_sample · Thresh)` with `m = ttcNumCubes atoms φ`.

Only the FPRAS parameter range is required; the shape hypotheses are the **two** the
input itself must satisfy — positivity and `Vol(F) > 0`.  No full-dimensionality
hypothesis is left (pruning *makes* it true, and it is not derivable,
`Ttc.hint_not_derivable`), and no boundedness hypothesis is left either: what the
chain needs is boundedness of the *pruned* `Sol`, and
`Ttc.isBounded_sol_pruneForm_of_volSol_pos` derives that from `hφ` and `hpos`. -/
theorem ttc_volume_api
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    (1 - δ ≤
      (∫⁻ c, trajLaw
            (runRates (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ)
              ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
              (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
              (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
              (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c)
          {t | ttcRunOutput (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ)
                    ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
                    (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
                    (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
                    (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t
                  / (ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos) ^ n
                ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (runCount (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ)
              ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
              (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
              (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos).thresh →
      Terminates (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t)
          (toDNFd (ttcInput atoms φ)) →
      runCost (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) cVol cSample
          (ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos) (toDNFd (ttcInput atoms φ))
        ≤ (toDNFd (ttcInput atoms φ)).length * (cVol + cSample * thr)) :=
  ttc_volume_prune atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ
    (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos) hpos

/-! ## The bridge to `Model/Pseudocode`

The input the run is on is `Model/Pseudocode`'s own `Ttc.preprocess`, by `rfl`.  The
companion bridge for the *measured* quantity, `Ttc.ttcEstimate_eq_ttcOutput`, is in
`Model/Theorem.lean` alongside `Ttc.ttcEstimate` itself. -/

/-- **The input the run is on is `Model/Pseudocode`'s `Ttc.preprocess`**, by `rfl`. -/
theorem ttcInput_eq_preprocess {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) :
    ttcInput atoms φ = preprocess atoms φ := rfl

end Api

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ttcInput_def
#print axioms Ttc.ttcInput_isPositive
#print axioms Ttc.ttcInput_bdd
#print axioms Ttc.ttcRadius_def
#print axioms Ttc.ttcScale_def
#print axioms Ttc.ttcAtoms_def
#print axioms Ttc.ttcAtoms_bdd
#print axioms Ttc.ttcCen_def
#print axioms Ttc.ttcScaledRadius_def
#print axioms Ttc.ttcBlock_def
#print axioms Ttc.ttcPrec_def
#print axioms Ttc.ttcOracleBundle_def
#print axioms Ttc.ttc_volume_api
#print axioms Ttc.ttcInput_eq_preprocess
