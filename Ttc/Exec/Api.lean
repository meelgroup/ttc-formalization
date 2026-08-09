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
