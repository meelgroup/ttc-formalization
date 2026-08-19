/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Ttc.Exec.BddFromPos

/-!
# `Exec/BddPrep`: the agreement lemma at the preprocessed formula

`Ttc.ttcAlgOutput` (`Model/Pseudocode`) and `Ttc.ttcEstimate` (`Exec/Api`) used to carry
four *proof*
binders — `hε0 : 0 < ε`, `hε1 : ε ≤ 1`, `hn : 1 ≤ n` and
`hbdd : Bornology.IsBounded (sol (atomSet atoms) (preprocess atoms φ))` — and every
one of them was consumed at exactly one place: `Ttc.inputParams`, because
`Ttc.Params` bundles five proof fields (`hε0 hε1 hn hm hr`) and so cannot be
*written down* without them.  Nothing else in the run reads a proof.

That obstruction is gone.  The block is now available as a function of the data
alone, and the definitions live in `Model/Pseudocode`, next to the run that reads
them:

* `Ttc.junkParams` — a `Ttc.Params` at constant data, the default value;
* `Ttc.ttcParamsTotal D n ε δ : Params` — `Ttc.ttcParams` guarded by a `dite` on the
  five side conditions, falling back on `Ttc.junkParams`;
* `Ttc.inputParamsTotal atoms φ ε δ : Params` — the same at the algorithm's inputs;
* `Ttc.ttcParamsTotal_eq`, `Ttc.ttcParamsTotal_eq_junk`,
  `Ttc.inputParamsTotal_eq_inputParams` — the agreement lemmas.

What stays **here** is the one of them that needs `Exec/`:
`Ttc.inputParamsTotal_preprocess`, the agreement lemma at the *preprocessed*
formula, whose boundedness side is discharged from `hφ` and `hpos` by
`Ttc.isBounded_sol_pruneForm_of_volSol_pos` (`Exec/BddFromPos`) and `Ttc.cleanBdd`
(`Exec/CleanInput`).  Whenever the side conditions hold, the total block *is* the
block the algorithm used to build — so replacing `inputParams` by
`inputParamsTotal` downstream changed no value that any theorem talks about, and the
four binders are deleted from `ttcAlgOutput` and `ttcEstimate`, and appear in
`Model/Theorem` only as plain hypotheses of the headline.

## Why the junk branch is inhabited at all

`Ttc.Params`' five proof fields constrain only its own scalar fields — `0 < ε`,
`ε ≤ 1`, `1 ≤ n`, `1 ≤ m`, `1 ≤ r` — and `ε δ n m r` are stored, not derived from
the formula.  So *no field is unsatisfiable at junk inputs*: `⟨1,1,1,1,1⟩` with
`le_refl`s is a `Params`.  What a junk block is not is *meaningful*: nothing relates
`junkParams.m` to the number of cubes.  That is exactly right — the agreement
lemmas say the junk branch is never taken under the theorem's hypotheses, and
nothing else is claimed about it.

## What this is *not*

It is **not** a route through `Ttc.isBounded_sol_pruneForm_of_volSol_pos`
(`Exec/BddFromPos`).  That theorem derives `hbdd` from `hpos`, which would replace
one proof binder by another — `0 < volSol (atomSet atoms) φ` is no more a piece of
data than boundedness is.  Only a total function of the data can carry zero proof
binders, so the guard has to be a `dite`; the boundedness theorem stays where it is
and is spent, as now, *inside proofs* (`Ttc.inputParamsTotal_preprocess` below is
where it is spent for the headline).
-/

namespace Ttc

section Total

variable {A : Type*}

/-! ## The agreement lemma at the preprocessed formula

`Ttc.junkParams`, `Ttc.ttcParamsTotal`, `Ttc.ttcParamsTotal_eq`,
`Ttc.ttcParamsTotal_eq_junk`, `Ttc.inputParamsTotal` and
`Ttc.inputParamsTotal_eq_inputParams` now live in `Model/Pseudocode`, where
`Ttc.ttcAlgOutput` and `Ttc.ttcEstimate` read them.  What stays here is the one lemma
that needs `Exec/`: the agreement lemma at the *preprocessed* formula, whose
boundedness proof is discharged from `hφ` and `hpos`. -/

/-- **The agreement lemma in the form the headline needs**: at the *preprocessed*
formula, with the boundedness proof discharged from `hφ` and `hpos` by
`Ttc.isBounded_sol_pruneForm_of_volSol_pos` (`Exec/BddFromPos`) and `Ttc.cleanBdd`
(`Exec/CleanInput`) — the same term `Ttc.preprocess_bdd` (`Exec/Api`) is.

So the block `Ttc.ttcAlgOutput` builds is a function of `(atoms, φ, ε, δ)` alone
wherever the theorem's own hypotheses hold, and the `hbdd` binder buys nothing that
`hpos` does not already buy inside a proof. -/
theorem inputParamsTotal_preprocess {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    inputParamsTotal atoms (preprocess atoms φ) ε δ
      = inputParams atoms (preprocess atoms φ) ε δ hε0 hε1 hn
          (preprocess_isPositive atoms φ)
          (cleanBdd atoms (isPositive_pruneForm atoms φ)
            (isBounded_sol_pruneForm_of_volSol_pos atoms hφ hpos)
            (pruneInt atoms hφ hpos)) :=
  inputParamsTotal_eq_inputParams _ _ _ _ hε0 hε1 hn _ _

end Total

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.inputParamsTotal_preprocess
