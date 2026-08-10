/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Ttc.Exec.BddFromPos

/-!
# `Exec/BddPrep`: the parameter block as a **total** function of the data

`Ttc.ttcAlgOutput` and `Ttc.ttcRun` (`Model/Pseudocode`) carry four *proof* binders
— `hε0 : 0 < ε`, `hε1 : ε ≤ 1`, `hn : 1 ≤ n` and
`hbdd : Bornology.IsBounded (sol (atomSet atoms) (preprocess atoms φ))` — and every
one of them is consumed at exactly one place: `Ttc.inputParams`, because
`Ttc.Params` bundles five proof fields (`hε0 hε1 hn hm hr`) and so cannot be
*written down* without them.  Nothing else in the run reads a proof.

This module removes that obstruction, by giving the block as a function of the data
alone:

* `Ttc.junkParams` — a `Ttc.Params` at constant data, the default value;
* `Ttc.ttcParamsTotal D n ε δ : Params` — `Ttc.ttcParams` guarded by a `dite` on the
  five side conditions, falling back on `Ttc.junkParams`;
* `Ttc.inputParamsTotal atoms φ ε δ : Params` — the same at the algorithm's inputs.

and, the point of the exercise, the **agreement lemmas**
`Ttc.ttcParamsTotal_eq`, `Ttc.inputParamsTotal_eq_inputParams` and
`Ttc.inputParamsTotal_preprocess`: whenever the side conditions hold, the total
block *is* the block the algorithm builds today — so replacing `inputParams` by
`inputParamsTotal` downstream changes no value that any theorem talks about, and
the four binders can then be deleted from `ttcAlgOutput` and `ttcRun` and restated
as plain inequalities in `Model/Theorem`.

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

/-! ## The default value -/

/-- **A `Ttc.Params` at constant data** — the junk value `Ttc.ttcParamsTotal` falls
back on when the side conditions fail.

Every field is a stored scalar and every proof field is `le_refl` or `one_pos`, so
this is unconditionally a `Params`.  It asserts nothing: no lemma below relates any
of its fields to a formula, and the agreement lemmas show it is never reached under
the hypotheses the headline carries. -/
noncomputable def junkParams : Params where
  ε := 1
  δ := 1
  n := 1
  m := 1
  r := 1
  hε0 := one_pos
  hε1 := le_refl 1
  hn := le_refl 1
  hm := le_refl 1
  hr := le_refl 1

/-! ## The guarded block -/

open scoped Classical in
/-- **The parameter block of `alg:ttc` lines 17–20, as a total function of the
data.**

`Ttc.ttcParams` needs five proofs; all five are propositions about `D`, `n` and `ε`
only, so they can be *decided* (classically) rather than supplied.  On the branch
where they hold this is literally `Ttc.ttcParams` (`Ttc.ttcParamsTotal_eq`); on the
other branch it is `Ttc.junkParams`, about which nothing is claimed.

This is the declaration that has to move into `Model/Pseudocode` for `Ttc.ttcRun`
to lose its proof binders.  It needs nothing beyond `Ttc.Params`, `Ttc.ttcParams`,
`Ttc.DNF` and `Ttc.FacetIndex`, all of which are in `Model/Prelude`. -/
noncomputable def ttcParamsTotal (D : DNF A) (n : ℕ) (ε δ : ℝ) : Params :=
  if h : 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ n ∧ 1 ≤ Nat.card {c : Cube A // c ∈ D} ∧
      1 ≤ Nat.card (FacetIndex D) then
    ttcParams D n ε δ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  else junkParams

/-- **The agreement lemma — the whole point.**  Where the five side conditions hold,
the total block *is* `Ttc.ttcParams` at the very same arguments.  The proofs
`hε0 … hr` occur on the right and not on the left, and by proof irrelevance the
right-hand side does not depend on which proofs they are; so every theorem stated
about `Ttc.ttcParams` transfers verbatim. -/
theorem ttcParamsTotal_eq (D : DNF A) (n : ℕ) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ D}) (hr : 1 ≤ Nat.card (FacetIndex D)) :
    ttcParamsTotal D n ε δ = ttcParams D n ε δ hε0 hε1 hn hm hr := by
  rw [ttcParamsTotal, dif_pos ⟨hε0, hε1, hn, hm, hr⟩]

/-- **The junk branch, named.**  Stated so that the fallback is visible as a
statement rather than only as a branch of the `dite`: if any side condition fails
the block is the default value, and in particular nothing about the formula can be
read off it. -/
theorem ttcParamsTotal_eq_junk (D : DNF A) (n : ℕ) (ε δ : ℝ)
    (h : ¬ (0 < ε ∧ ε ≤ 1 ∧ 1 ≤ n ∧ 1 ≤ Nat.card {c : Cube A // c ∈ D} ∧
      1 ≤ Nat.card (FacetIndex D))) :
    ttcParamsTotal D n ε δ = junkParams := by
  rw [ttcParamsTotal, dif_neg h]

/-! ## At the algorithm's own inputs -/

/-- **`Ttc.inputParams` as a total function of the data.**

`Ttc.inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd` is `Ttc.ttcParams (toDNFd φ) n ε
(4δ/5)` with `hm` and `hr` derived from `hφ` and `hbdd`; its *data* never mentions
`atoms`, which enters only through those two derivations.  The `atoms` binder is
kept so that this is a drop-in replacement at the call sites. -/
noncomputable def inputParamsTotal {n : ℕ} (_atoms : A → LinAtom n) (φ : BForm A)
    (ε δ : ℝ) : Params :=
  ttcParamsTotal (toDNFd φ) n ε (4 * δ / 5)

/-- **The agreement lemma at the algorithm's inputs.**  Under the four hypotheses
the headline already carries — three plain inequalities and boundedness — the total
block is `Ttc.inputParams`. -/
theorem inputParamsTotal_eq_inputParams {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ)) :
    inputParamsTotal atoms φ ε δ = inputParams atoms φ ε δ hε0 hε1 hn hφ hbdd :=
  ttcParamsTotal_eq _ _ _ _ hε0 hε1 hn _ _

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

#print axioms Ttc.junkParams
#print axioms Ttc.ttcParamsTotal
#print axioms Ttc.ttcParamsTotal_eq
#print axioms Ttc.ttcParamsTotal_eq_junk
#print axioms Ttc.inputParamsTotal
#print axioms Ttc.inputParamsTotal_eq_inputParams
#print axioms Ttc.inputParamsTotal_preprocess
