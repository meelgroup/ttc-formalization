/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.BddFromPos

/-!
# `Exec/Api`: the statement API — the *auxiliary* layer, and the headline restated

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
`Ttc.runScale` and `Ttc.scaledAtoms` internally.  `Ttc.ttc_volume_api`'s proof is
one application of `Ttc.ttc_volume_prune`.

## What stayed here, and what moved to `Model/Run`

**The quantities the headline *names* are no longer in this file.**  They are in
`Ttc/Model/Run.lean`, the fifth file of the audit surface, which imports this one:

* the seven measured quantities — `Ttc.ttcIndex`, `Ttc.ttcRates`,
  `Ttc.ttcEstimate`, `Ttc.ttcThresh`, `Ttc.ttcTerminates`, `Ttc.ttcCost`,
  `Ttc.ttcNumCubes` — with their `rfl` lemmas and the bridge
  `Ttc.ttcEstimate_eq_ttcOutput`;
* the five auxiliaries the headline's statement also names — `Ttc.ttcInput`,
  `Ttc.ttcScale`, `Ttc.ttcBlock`, `Ttc.ttcPrec`, `Ttc.ttcOracleBundle` — with
  their `rfl` lemmas and the bridge `Ttc.ttcInput_eq_preprocess`.

That move is what lets `Model/Theorem.lean` be **one declaration** and still name
nothing outside `Model/`.  What is left here is the layer those bodies are built
*from*, which the headline does not name:

* `Ttc.ttcRadius` — the `GetPrecision` inscribed radius `Ttc.autoGamma` of the
  preprocessed formula;
* `Ttc.ttcAtoms` — the dilated input, the `A → LinAtom n` the run wrappers are
  applied to;
* `Ttc.ttcCen` — the dilated inscribed-ball centres;
* `Ttc.ttcScaledRadius` — the inscribed radius *after* the dilation, which is the
  `γ̂` every run wrapper takes;
* the three obligations these discharge from the headline's own binders,
  `Ttc.ttcInput_isPositive`, `Ttc.ttcInput_bdd`, `Ttc.ttcAtoms_bdd`;
* `Ttc.ttc_volume_api`, the headline restated, which is what
  `Ttc.ttc_volume_estimate` is a bare application of.

Since `Ttc.ttcInput`, `Ttc.ttcScale`, `Ttc.ttcBlock`, `Ttc.ttcPrec` and
`Ttc.ttcOracleBundle` are downstream of this file, the statements below spell out
their bodies instead of naming them — `cleanForm atoms (pruneForm atoms φ)` for
the input, `Ttc.runScale …` for the dilation, `Ttc.inputParams …` for the block,
`Ttc.runPrec …` for the precision and `Ttc.runOracles …` for the bundle.  Each is
*definitionally* the corresponding `Model/Run` name (that is exactly what the
`_def` lemmas there say), which is why `Ttc.ttc_volume_estimate` can be stated
over the names and proved by applying `Ttc.ttc_volume_api`, with no rewriting.

## What the algorithm is actually handed

Two preprocessing passes stand between the user's formula and the run, and
`Ttc.ttcInput` (`Model/Run`) is their composite:

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
in `Ttc.ttc_volume_api`'s conclusion is at the preprocessed formula — that is what
the algorithm runs on — *except* the accuracy conjunct, which compares the estimate
with `volSol (atomSet atoms) φ` at the user's own `φ`.  Nothing post-processes the
estimate to make that work: `Ttc.volSol_pruneForm` and `Ttc.volSol_cleanForm` say
the two volumes are equal.

## Nothing here is an assumption

**Every `def` in this file is a pure abbreviation and asserts nothing.**  Each is a
`def` whose body is a closed term, and each carries an identifying `rfl` lemma
(`Ttc.ttcRadius_def`, `Ttc.ttcAtoms_def`, `Ttc.ttcCen_def`,
`Ttc.ttcScaledRadius_def`) spelling out that body, proved by `rfl`.  So no name in
this file stands in for a proof: what a name means is exhibited, machine-checked,
next to the name.

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
-/

namespace Ttc

open MeasureTheory Set Pointwise

section Api

variable {A : Type*} {n : ℕ}

/-! ## The two obligations the preprocessed formula discharges

`Ttc.pruneForm` then `Ttc.cleanForm` — the formula `Model/Run` names
`Ttc.ttcInput` — with the two obligations the run wrappers ask of it discharged
from the headline's own binders. -/

/-- The preprocessed formula is positive — unconditionally, both passes rebuilding
the formula from `Ttc.dnfForm`.  Stated at `cleanForm atoms (pruneForm atoms φ)`,
which is `Ttc.ttcInput atoms φ` (`Model/Run`) by `rfl`. -/
theorem ttcInput_isPositive (atoms : A → LinAtom n) (φ : BForm A) :
    (cleanForm atoms (pruneForm atoms φ)).IsPositive :=
  isPositive_cleanForm atoms (pruneForm atoms φ)

/-- `Sol` of the preprocessed formula is bounded — `Ttc.cleanBdd` over
`Ttc.isBounded_sol_pruneForm_of_volSol_pos`/`Ttc.pruneInt`, so `hφ` and `hpos` are
all that is spent.  No boundedness hypothesis: it is *derived* from `hpos` at the
pruned formula (`Exec/BddFromPos`). -/
theorem ttcInput_bdd (atoms : A → LinAtom n) (φ : BForm A) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    Bornology.IsBounded (sol (atomSet atoms) (cleanForm atoms (pruneForm atoms φ))) :=
  cleanBdd atoms (isPositive_pruneForm atoms φ)
    (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos) (pruneInt atoms hφ hpos)

/-! ## The inscribed-ball data and the dilation

Four abbreviations for the terms `Exec/Rescaled`'s wrappers are applied to inside
`Ttc.ttc_volume_prune`.  All four are at the preprocessed formula. -/

/-- **The inscribed radius `GetPrecision` computes** for the preprocessed formula:
`Ttc.autoGamma` at `Ttc.ttcInput atoms φ`. -/
noncomputable def ttcRadius (atoms : A → LinAtom n) (φ : BForm A) : ℝ :=
  autoGamma atoms (cleanForm atoms (pruneForm atoms φ))

theorem ttcRadius_def (atoms : A → LinAtom n) (φ : BForm A) :
    ttcRadius atoms φ = autoGamma atoms (cleanForm atoms (pruneForm atoms φ)) := rfl

/-- **The dilated input** — the preprocessed formula's atoms with their bounds
scaled by `Ttc.ttcScale` (`Model/Run`; written out here as `Ttc.runScale …`, since
that name is downstream).  This is the `A → LinAtom n` the run wrappers are applied
to. -/
noncomputable def ttcAtoms (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : A → LinAtom n :=
  scaledAtoms atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
    (ttcInput_isPositive atoms φ) (ttcInput_bdd atoms φ hφ hpos) (ttcRadius atoms φ)

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
      (sol (atomSet (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos))
        (cleanForm atoms (pruneForm atoms φ))) :=
  scaledBdd atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
    (ttcInput_isPositive atoms φ) (ttcInput_bdd atoms φ hφ hpos) (ttcRadius atoms φ)

/-- **The dilated centres** — `Ttc.autoCen` at the preprocessed formula, moved by
the dilation, so that each dilated cube's inscribed ball is centred correctly. -/
noncomputable def ttcCen (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    {c : Cube A // c ∈ toDNFd (cleanForm atoms (pruneForm atoms φ))} → Space n :=
  fun i =>
    runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
        (ttcInput_isPositive atoms φ) (ttcInput_bdd atoms φ hφ hpos) (ttcRadius atoms φ)
      • autoCen atoms (cleanForm atoms (pruneForm atoms φ)) i

theorem ttcCen_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos
      = fun i =>
          runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
              (isPositive_cleanForm atoms (pruneForm atoms φ))
              (cleanBdd atoms (isPositive_pruneForm atoms φ)
                (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos)
                (pruneInt atoms hφ hpos))
              (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
            • autoCen atoms (cleanForm atoms (pruneForm atoms φ)) i := rfl

/-- **The inscribed radius after the dilation**, `ttcScale * ttcRadius` — the `γ̂`
every run wrapper of `Exec/Inputs` is applied to. -/
noncomputable def ttcScaledRadius (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) : ℝ :=
  runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
      (ttcInput_isPositive atoms φ) (ttcInput_bdd atoms φ hφ hpos) (ttcRadius atoms φ)
    * ttcRadius atoms φ

theorem ttcScaledRadius_def (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos
      = runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
            (isPositive_cleanForm atoms (pruneForm atoms φ))
            (cleanBdd atoms (isPositive_pruneForm atoms φ)
              (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos)
              (pruneInt atoms hφ hpos))
            (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
          * autoGamma atoms (cleanForm atoms (pruneForm atoms φ)) := rfl

/-! ## The headline, restated

Same theorem as `Ttc.ttc_volume_prune`, same conclusion — only spelled with the
names above, and with the pruned-boundedness argument supplied rather than assumed,
so this statement has **eleven** binders.  The proof is the single application; it
typechecks exactly when every definition of this module is definitionally the
sub-term it names.

The parameter block, the precision, the oracle bundle, the dilation and the
preprocessed formula are written out here rather than named, because their names —
`Ttc.ttcBlock`, `Ttc.ttcPrec`, `Ttc.ttcOracleBundle`, `Ttc.ttcScale`,
`Ttc.ttcInput` — and the seven measured quantities built on them are introduced in
`Model/Run`, which imports this file.  Each sub-term here is *literally* the body
of the corresponding definition there, so `Ttc.ttc_volume_estimate` is this theorem
applied, with no rewriting. -/

/-- **`thm:volumettc` + `thm:runtime`, in the statement API.**  `TTC(F, ε, δ)` run
on `φ` — with the two preprocessing passes (`Ttc.pruneForm`, `Ttc.cleanForm`), the
inscribed-ball construction (`Ttc.autoCen`/`Ttc.autoGamma`), the dilation
(`Ttc.runScale`) and the parameter block (`Ttc.inputParams`) all internal to the
statement.

* **Accuracy.**  `Pr[ estimate ∈ (1 ± ε)·Vol(Sol φ) ] ≥ 1 − δ`, over the joint
  law of the volume coins `Ttc.MonteCarlo.coins` and the sample trajectory.  The
  target is the volume of the **original** body: neither preprocessing pass moves
  it.

* **Running time.**  On every run `(c, t)` whose absorption loops exit, the charged
  cost is at most `m · (C_vol + C_sample · Thresh)` with `m` the preprocessed
  formula's cube count.

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
            (runRates (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
              (cleanForm atoms (pruneForm atoms φ))
              ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
              (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
              (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
              (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c)
          {t | ttcRunOutput (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
                    (cleanForm atoms (pruneForm atoms φ))
                    ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
                    (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
                    (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
                    (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t
                  / (runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
                      (ttcInput_isPositive atoms φ) (ttcInput_bdd atoms φ hφ hpos)
                      (ttcRadius atoms φ)) ^ n
                ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (runCount (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
              (cleanForm atoms (pruneForm atoms φ))
              ε δ hε0 hε1 hn (ttcInput_isPositive atoms φ)
              (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
              (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ)
          = (inputParams atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
              (ttcInput_isPositive atoms φ) (ttcInput_bdd atoms φ hφ hpos)).thresh →
      Terminates
          (inputParams atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
            (ttcInput_isPositive atoms φ) (ttcInput_bdd atoms φ hφ hpos))
          (runOracles (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
            (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
            (ttcInput_isPositive atoms φ)
            (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
            (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
            (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t)
          (toDNFd (cleanForm atoms (pruneForm atoms φ))) →
      runCost
          (inputParams atoms (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
            (ttcInput_isPositive atoms φ) (ttcInput_bdd atoms φ hφ hpos))
          (runOracles (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
            (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
            (ttcInput_isPositive atoms φ)
            (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
            (ttcCen atoms φ ε δ hε0 hε1 hn hφ hpos)
            (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos) c t)
          cVol cSample
          (runPrec (ttcAtoms atoms φ ε δ hε0 hε1 hn hφ hpos)
            (cleanForm atoms (pruneForm atoms φ)) ε δ hε0 hε1 hn
            (ttcInput_isPositive atoms φ)
            (ttcAtoms_bdd atoms φ ε δ hε0 hε1 hn hφ hpos)
            (ttcScaledRadius atoms φ ε δ hε0 hε1 hn hφ hpos))
          (toDNFd (cleanForm atoms (pruneForm atoms φ)))
        ≤ (toDNFd (cleanForm atoms (pruneForm atoms φ))).length
            * (cVol + cSample * thr)) :=
  ttc_volume_prune atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ
    (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos) hpos

end Api

/-! # The quantities the headline names

`Ttc/Model/Run.lean` used to hold these twelve abbreviations, as a fifth file of the
audit surface.  It is gone: `Model/` is the four files `Prelude`, `ProblemSetting`,
`Pseudocode`, `Theorem`, and the algorithm itself — including its output
`Ttc.ttcAlgOutput` — is in `Model/Pseudocode`.  What is left here is the *run's*
vocabulary: the constructed oracle bundle, the law its sample coins are drawn from,
and the four folded names of the runtime conjunct.

**Every `def` below is a pure abbreviation and asserts nothing.**  Each has a closed
body and an identifying `rfl` lemma (`Ttc.ttcInput_def`, `Ttc.ttcScale_def`, …)
spelling that body out, so no name here stands in for a proof.  The structural check
that they are the *right* abbreviations is that `Ttc.ttc_volume_estimate`'s proof is
the bare application `Ttc.ttc_volume_api atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hpos`, with
no rewriting — a wrong abbreviation is a build error, not a silent divergence. -/

section Measured

variable {A : Type*} {n : ℕ}

open MeasureTheory Set Pointwise

/-- **The formula `TTC` is actually run on** — the user's `φ` with its degenerate
cubes pruned (`Ttc.pruneForm`) and its zero-normal atoms cleaned (`Ttc.cleanForm`).
This is `Ttc.preprocess` of `Model/Pseudocode` (`Ttc.ttcInput_eq_preprocess`, by
`rfl`).  `Ttc.volSol` is unchanged by both passes (`Ttc.volSol_pruneForm`,
`Ttc.volSol_cleanForm`), so the accuracy target stays the original `Vol(F)`. -/
noncomputable def ttcInput (atoms : A → LinAtom n) (φ : BForm A) : BForm A :=
  cleanForm atoms (pruneForm atoms φ)

theorem ttcInput_def (atoms : A → LinAtom n) (φ : BForm A) :
    ttcInput atoms φ = cleanForm atoms (pruneForm atoms φ) := rfl

/-- **The input the run is on is `Model/Pseudocode`'s `Ttc.preprocess`**, by `rfl`. -/
theorem ttcInput_eq_preprocess (atoms : A → LinAtom n) (φ : BForm A) :
    ttcInput atoms φ = preprocess atoms φ := rfl

variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)

/-- **`Sol` of the preprocessed formula is bounded**, derived from `hφ` and `hpos`
alone (`Ttc.isBounded_sol_pruneForm_of_volSol_pos`, `Exec/BddFromPos`, then
`Ttc.cleanBdd`).  Stated at `Ttc.preprocess atoms φ`, which is `Ttc.ttcInput atoms φ`
by `rfl`.

**This is the one proof term `Ttc.ttc_volume_estimate`'s type names outside
`Model/`.**  It has to: `Ttc.Params` bundles five proof fields, so `Ttc.inputParams`
— and hence `Ttc.ttcAlgOutput`, the algorithm's own output — cannot be applied
without a proof of this.  `Model/Pseudocode`'s docstring, "The divergence from the
reference layout", says why that is not fixable without a large refactor. -/
theorem preprocess_bdd (atoms : A → LinAtom n) (φ : BForm A) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    Bornology.IsBounded (sol (atomSet atoms) (preprocess atoms φ)) :=
  ttcInput_bdd atoms φ hφ hpos

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

/-! ## The run's index, oracle bundle, rates and estimate -/

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

/-! ## The four folded names of the runtime conjunct -/

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

/-! ## The two bridges to `Model/Pseudocode`

The first is what makes `Ttc.ttc_volume_estimate` a statement about the *algorithm*:
the measured quantity is `Model/Pseudocode`'s own `Ttc.ttcAlgOutput`, at the oracle
bundle the run reads, and the identification is `rfl` — checked by the kernel, not
asserted in prose. -/

/-- **The measured quantity is `Model/Pseudocode`'s `Ttc.ttcAlgOutput` at the run's
oracle bundle**, by `rfl`.  `Ttc.ttcAlgOutput` folds `Ttc.run` over
`Ttc.toDNFd (Ttc.preprocess atoms φ)` at `Ttc.inputParams` and `Ttc.runPrec` and
divides by `qⁿ`; `Ttc.ttcEstimate` is the same term with the constructed bundle
already applied.  `Model/Theorem.lean`'s accuracy conjunct is stated with the
left-hand side. -/
theorem ttcAlgOutput_eq_ttcEstimate (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) :
    ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
        (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t)
      = ttcEstimate atoms φ ε δ hε0 hε1 hn hφ hpos c t := rfl

/-- **The measured quantity is also `Model/Pseudocode`'s `Ttc.ttcOutput`, divided by
`qⁿ`** — lines A12–A13 of the preprocessing transcription, by `rfl`.  The
oracle-bundle-free form of the bridge above. -/
theorem ttcEstimate_eq_ttcOutput (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) :
    ttcEstimate atoms φ ε δ hε0 hε1 hn hφ hpos c t
      = ttcOutput (ttcBlock atoms φ ε δ hε0 hε1 hn hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c) toDNFd
          (ttcPrec atoms φ ε δ hε0 hε1 hn hφ hpos) (ttcInput atoms φ) t
        / (ttcScale atoms φ ε δ hε0 hε1 hn hφ hpos) ^ n := rfl

/-! ## The oracle-free form of the algorithm's output

`Ttc.ttcRun` (`Model/Pseudocode`) is `Ttc.ttcAlgOutput` with its oracle argument
filled in from the run `(c, t)` itself, built inline from the read-offs
`Ttc.trajThin`, `Ttc.trajPois`, `Ttc.trajGen`, `Ttc.padRow` and the Monte-Carlo
volume estimator `Ttc.mcVol` — all of which are defined in `Model/Pseudocode`.

The two lemmas below are what make that an honest definition rather than a rename:
the index it is stated over *is* `Ttc.ttcIndex`, and the number it returns *is*
`Ttc.ttcAlgOutput` at `Ttc.ttcOracleBundle`.  Both hold by `rfl`, so the two terms
are not merely provably equal — they are the same term, and a divergence would be a
build error rather than a silent drift. -/

/-- **The `Model/`-side index is the run's index**, by `rfl`.  `Ttc.ttcIndex`
(above) reads `Ttc.runCount` at the dilated atoms and the dilated boundedness proof;
`Ttc.algIndex` (`Model/Pseudocode`) reads `Ttc.latticeCount` at the dilated atoms and
`Ttc.runPrec` at the *original* boundedness proof, which is legitimate because
`Ttc.inputParams_scaleAtoms` holds definitionally.  So `Ttc.ttcRun` needs no second
boundedness binder. -/
theorem algIndex_eq_ttcIndex :
    algIndex atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
      = ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos := rfl

/-- **`Ttc.ttcRun` is `Ttc.ttcAlgOutput` at the constructed oracle bundle**, by
`rfl`.

This is the lemma the headline rests on: `Model/Theorem`'s accuracy conjunct is
stated over `Ttc.ttcRun`, which names nothing outside `Model/`, and this identifies
it with the oracle-bundle form the rest of the development proves things about.
`Ttc.ttc_accuracy_single_measure` is transported through it by nothing at all — the
two sides are definitionally equal, so the proof term is unchanged. -/
theorem ttcRun_eq_ttcAlgOutput (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) :
    ttcRun atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos) c t
      = ttcAlgOutput atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos)
          (ttcOracleBundle atoms φ ε δ hε0 hε1 hn hφ hpos c t) := rfl

/-- **`Ttc.ttcRun` is the run's estimate**, by `rfl` — the oracle-free form of
`Ttc.ttcAlgOutput_eq_ttcEstimate`. -/
theorem ttcRun_eq_ttcEstimate (c : ℕ → Space n)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ hε0 hε1 hn hφ hpos) → ℕ) :
    ttcRun atoms φ ε δ hε0 hε1 hn (preprocess_bdd atoms φ hφ hpos) c t
      = ttcEstimate atoms φ ε δ hε0 hε1 hn hφ hpos c t := rfl

end Measured

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ttcInput_isPositive
#print axioms Ttc.ttcInput_bdd
#print axioms Ttc.ttcRadius_def
#print axioms Ttc.ttcAtoms_def
#print axioms Ttc.ttcAtoms_bdd
#print axioms Ttc.ttcCen_def
#print axioms Ttc.ttcScaledRadius_def
#print axioms Ttc.ttc_volume_api
#print axioms Ttc.ttcInput_def
#print axioms Ttc.ttcInput_eq_preprocess
#print axioms Ttc.preprocess_bdd
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
#print axioms Ttc.ttcAlgOutput_eq_ttcEstimate
#print axioms Ttc.ttcEstimate_eq_ttcOutput
#print axioms Ttc.algIndex_eq_ttcIndex
#print axioms Ttc.ttcRun_eq_ttcAlgOutput
#print axioms Ttc.ttcRun_eq_ttcEstimate
