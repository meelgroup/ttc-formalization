/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Ttc.Exec.CleanInput
import Ttc.Exec.Degenerate

/-!
# `Exec/Prune`: `hint` discharged by construction, at the price of a null set

`Ttc.ttc_volume_cleanInput` (`Exec/CleanInput`) still carries

```
hint : ∀ i : {c : Cube A // c ∈ toDNFd φ}, (interior (region (atomSet atoms) i.val)).Nonempty
```

— *every polytope of the decomposition is full-dimensional*.  This module replaces
it by the strictly weaker

```
hpos : 0 < volSol (atomSet atoms) φ
```

— *the body has positive volume* — without adding a binder.

## `hint` is **not** derivable, so it is discharged **by construction**

`Ttc.hint_not_derivable` (`Exec/Degenerate`) is a machine-checked refutation: the
formula `Ttc.degForm` = `(x ≤ 0 ∧ −x ≤ 0) ∨ (x ≤ 1 ∧ −x ≤ 1)` in dimension `1` is
negation-free, has bounded solution set `[−1, 1]`, has no atom with a zero normal,
and has `0 < Vol(F)` — yet its DNF's first cube denotes the single point `{0}`, so
`hint` fails.  In particular `hpos` really is **strictly** weaker than `hint`:
`hint` implies `hpos` for a bounded body (`Ttc.volSol_pos_of_interior`, proved below),
while `Ttc.degForm` satisfies `hpos` and refutes `hint`.  Both directions are
machine-checked; neither is left to prose.

So `hint` cannot be deleted; it has to be *made true*.  The move is to run `TTC` not
on `φ` but on `φ` with its degenerate cubes pruned away:

```
pruneForm atoms φ := dnfForm (nondegenCubes (atomSet atoms) (toDNFd φ))
```

Every cube of the pruned DNF has nonempty interior by the very definition of
`Ttc.nondegenCubes`, so `hint` holds for `Ttc.pruneForm atoms φ` outright
(`Ttc.interior_nonempty_pruneForm`), with no hypothesis beyond `hφ` and
non-emptiness of the pruned list.

## Why the formula has to move with the DNF

Exactly as in `Exec/Cleanup`.  Pruning the DNF *in place* and leaving `φ` alone is
unavailable: `Ttc.IsDNFOf D φ` quantifies over **all** Boolean assignments, and
`Ttc.not_isDNFOf_nondegenCubes_degForm` refutes the naive statement on `Ttc.degForm`
— the assignment `v a ↔ a ∈ {0, 1}` satisfies `degForm` and no surviving cube.  So
the *formula* is rebuilt from the surviving cubes, `Ttc.dnfForm`-style, which is a
genuine `Ttc.IsDNFOf` of itself (`Ttc.isDNFOf_dnfForm`).  `Ttc.cleanForm` is the
template; this file follows it step for step.

## The one difference from `Ttc.cleanForm`: `sol` moves, `volSol` does not

`Ttc.sol_cleanForm` is an equality of **sets** — cleaning deletes literals denoting
`Set.univ` and cubes denoting `∅`, so the body is literally unchanged.  Pruning is
**not** like that: it deletes cubes whose region is nonempty but lower-dimensional,
so

```
sol (atomSet atoms) (pruneForm atoms φ) ⊊ sol (atomSet atoms) φ    -- in general
```

and only the inclusion `⊆` is available (`Ttc.sol_pruneForm_subset`) — enough to
transport `hbdd` *into* the pruned formula (`Ttc.isBounded_sol_pruneForm`,
`Ttc.pruneBdd`), not enough to transport anything stated as a set equality.  Note the
transport is not needed by the chain: `Ttc.ttc_volume_prune` asks for boundedness of
the **pruned** `Sol` and `Exec/BddFromPos` derives that from `hφ` and `hpos` alone.
What *is* preserved is the measure: the deleted regions
are convex with empty interior, hence Lebesgue-null, and there are finitely many of
them (`Ttc.volume_sol_eq_volume_biUnion_nondegenCubes`), so

```
volSol (atomSet atoms) (pruneForm atoms φ) = volSol (atomSet atoms) φ
```

(`Ttc.volSol_pruneForm`).  **This is sound only because the conclusion of
`thm:volumettc` merely *measures* `Sol(F)`**: the accuracy conjunct asks that the
estimate land in `relErr ε (volSol (atomSet atoms) φ)`, and `Ttc.volSol` is a
measure, blind to the null difference.  Had the conclusion mentioned `Ttc.sol`
itself — as the lattice-side development does, which is why `Exec/Degenerate`
records the pruning repair as unavailable *there* — the substitution would be
illegitimate.

## What the run is handed

`Ttc.ttc_volume_prune` is `Ttc.ttc_volume_cleanInput` at `ψ := pruneForm atoms φ`.
Every mention of the formula in the conclusion is at the pruned formula — that *is*
what the algorithm is handed — except the accuracy target, which is rewritten back
to the **original** `volSol (atomSet atoms) φ` by `Ttc.volSol_pruneForm`.  No
estimate is post-processed and no scalar is chosen; contrast `Exec/Rescaled`, where
`Sol(F)` genuinely dilates and the estimate is divided by `cⁿ` afterwards.

## The side condition, and where `hpos` is spent

The `Ttc.dnfForm` results all need the pruned list to be nonempty — `Ttc.dnfForm []`
is the junk value `BForm.tt`.  That is precisely what `hpos` buys: if no cube
survived, the pruned union would be empty, so `Vol(F) = 0`
(`Ttc.nondegenCubes_ne_nil_of_volSol_pos`).  `hpos` is used for nothing else.
-/

namespace Ttc

open MeasureTheory Set

section Prune

variable {A : Type*} {n : ℕ}

/-! ## The pruned formula

`Ttc.pruneForm atoms φ = dnfForm (nondegenCubes (atomSet atoms) (toDNFd φ))` is
lines A2–A3 of the preprocessing, and it is **defined in `Model/Pseudocode`**
alongside every other step of the amended algorithm — the audit path carries the
definition, this file carries what is proved about it. -/

/-- The pruned formula is positive, so `hφ` survives it — unconditionally, since
`Ttc.dnfForm` is built from `.or`, `.and`, `.atom` and `.tt` only. -/
theorem isPositive_pruneForm (atoms : A → LinAtom n) (φ : BForm A) :
    (pruneForm atoms φ).IsPositive := isPositive_dnfForm _

/-- Pruning only removes cubes, so positivity of the DNF is inherited. -/
theorem isPositive_nondegenCubes (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive) :
    DNF.IsPositive (nondegenCubes (atomSet atoms) (toDNFd φ)) :=
  fun _ hc => toDNFd_isPositive hφ _ (nondegenCubes_subset hc)

/-! ## `hpos` buys exactly the side condition `Ttc.dnfForm` needs -/

/-- **The pruned DNF is nonempty whenever `Vol(F) > 0`.**

If every cube were degenerate the pruned union would be empty, and
`Ttc.volume_sol_eq_volume_biUnion_nondegenCubes` says `Sol(F)` has that union's
measure — so `Vol(F)` would be `0`.  This is the *only* place `hpos` is used. -/
theorem nondegenCubes_ne_nil_of_volSol_pos (atoms : A → LinAtom n) {φ : BForm A}
    (hD : IsDNFOf (toDNFd φ) φ) (h : 0 < volSol (atomSet atoms) φ) :
    nondegenCubes (atomSet atoms) (toDNFd φ) ≠ [] := by
  intro hnil
  have h0 : volume (sol (atomSet atoms) φ) = 0 := by
    rw [volume_sol_eq_volume_biUnion_nondegenCubes atoms hD, hnil]
    simp
  rw [volSol, h0] at h
  simp at h

/-- The same, with the (always available) `Ttc.toDNFd_isDNFOf` supplied. -/
theorem pruneNeNil (atoms : A → LinAtom n) {φ : BForm A}
    (hpos : 0 < volSol (atomSet atoms) φ) :
    nondegenCubes (atomSet atoms) (toDNFd φ) ≠ [] :=
  nondegenCubes_ne_nil_of_volSol_pos atoms (toDNFd_isDNFOf φ) hpos

/-! ## `hpos` is **strictly** weaker than `hint` -/

/-- **`hint` implies `hpos`** for a bounded body: `hφ` supplies a cube
(`Ttc.toDNFd_ne_nil`), `hint` supplies a point of its interior, openness of the
interior supplies a ball around that point inside `Sol(F)`, and a ball has positive
volume; `hbdd` keeps the total finite so that `.toReal` does not collapse.

Together with `Ttc.hint_not_derivable` — which exhibits `Ttc.degForm`, satisfying
`hφ`, `hbdd` and `0 < volSol` while **failing** `hint` — this makes the trade of
`hint` for `hpos` a strict weakening in both directions, machine-checked. -/
theorem volSol_pos_of_interior (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))
    (hint : ∀ i : {c : Cube A // c ∈ toDNFd φ},
      (interior (region (atomSet atoms) i.val)).Nonempty) :
    0 < volSol (atomSet atoms) φ := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (toDNFd_ne_nil hφ)
  obtain ⟨x, hx⟩ := hint ⟨c, hc⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hsub : Metric.ball x r ⊆ sol (atomSet atoms) φ :=
    (hball.trans interior_subset).trans (region_subset_sol (toDNFd_isDNFOf φ) hc)
  refine ENNReal.toReal_pos ?_ hbdd.measure_lt_top.ne
  intro h0
  exact (Metric.measure_ball_pos volume x hr).ne'
    (nonpos_iff_eq_zero.1 (h0 ▸ measure_mono hsub))

/-! ## The pruned formula's own DNF -/

/-- **The pruned formula is a genuine `Ttc.IsDNFOf` of the surviving cubes** — this
is the repair that makes the substitution legitimate at all. -/
theorem isDNFOf_pruneForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : nondegenCubes (atomSet atoms) (toDNFd φ) ≠ []) :
    IsDNFOf (nondegenCubes (atomSet atoms) (toDNFd φ)) (pruneForm atoms φ) :=
  isDNFOf_dnfForm hne (isPositive_nondegenCubes atoms hφ)

/-- **The pruned formula's DNF is exactly the surviving cube list.** -/
theorem toDNF_pruneForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : nondegenCubes (atomSet atoms) (toDNFd φ) ≠ []) :
    toDNF (pruneForm atoms φ) = nondegenCubes (atomSet atoms) (toDNFd φ) :=
  toDNF_dnfForm hne (isPositive_nondegenCubes atoms hφ)

/-- …and so does its deduplicated DNF, up to membership — which is all that `hint`
and `Ttc.FacetIndex` ever see. -/
theorem mem_toDNFd_pruneForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : nondegenCubes (atomSet atoms) (toDNFd φ) ≠ []) {c : Cube A} :
    c ∈ toDNFd (pruneForm atoms φ) ↔ c ∈ nondegenCubes (atomSet atoms) (toDNFd φ) := by
  rw [mem_toDNFd, toDNF_pruneForm atoms hφ hne]

/-- **`hint`, discharged by construction.**  A cube of the pruned formula's DNF is a
cube that survived `Ttc.nondegenCubes`, and surviving *is* having nonempty interior
(`Ttc.mem_nondegenCubes`).  No degeneracy hypothesis on `φ` at all. -/
theorem interior_nonempty_pruneForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : nondegenCubes (atomSet atoms) (toDNFd φ) ≠ []) :
    ∀ i : {c : Cube A // c ∈ toDNFd (pruneForm atoms φ)},
      (interior (region (atomSet atoms) i.val)).Nonempty := by
  rintro ⟨c, hc⟩
  exact (mem_nondegenCubes.1 ((mem_toDNFd_pruneForm atoms hφ hne).1 hc)).2

/-! ## What pruning does and does not preserve -/

/-- The pruned formula denotes the union of the surviving regions. -/
theorem sol_pruneForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : nondegenCubes (atomSet atoms) (toDNFd φ) ≠ []) :
    sol (atomSet atoms) (pruneForm atoms φ)
      = ⋃ c ∈ nondegenCubes (atomSet atoms) (toDNFd φ), region (atomSet atoms) c :=
  (sol_eq_iUnion_region (isDNFOf_pruneForm atoms hφ hne)).symm

/-- **`Sol` shrinks, and only shrinks.**  Note this is a genuine `⊆` and *not* an
equality — `Ttc.thinCube` shows the inclusion can be strict, which is exactly why
this file proves a `Ttc.volSol` equality instead of a `Ttc.sol` equality. -/
theorem sol_pruneForm_subset (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : nondegenCubes (atomSet atoms) (toDNFd φ) ≠ []) :
    sol (atomSet atoms) (pruneForm atoms φ) ⊆ sol (atomSet atoms) φ := by
  rw [sol_pruneForm atoms hφ hne]
  exact Set.iUnion₂_subset fun _ hc =>
    region_subset_sol (toDNFd_isDNFOf φ) (nondegenCubes_subset hc)

/-- **`hbdd` for the pruned formula.**  A subset of a bounded set is bounded; unlike
`Ttc.cleanBdd` this does not go through a set *equality*. -/
theorem isBounded_sol_pruneForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : nondegenCubes (atomSet atoms) (toDNFd φ) ≠ [])
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ)) :
    Bornology.IsBounded (sol (atomSet atoms) (pruneForm atoms φ)) :=
  hbdd.subset (sol_pruneForm_subset atoms hφ hne)

/-- **The volume is untouched.**  The pruned cubes have convex regions with empty
interior, hence Lebesgue measure zero, and there are finitely many of them
(`Ttc.volume_sol_eq_volume_biUnion_nondegenCubes`).  This is what makes replacing
`hint` by `hpos` sound: the theorem's conclusion only ever *measures* `Sol(F)`. -/
theorem volSol_pruneForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : nondegenCubes (atomSet atoms) (toDNFd φ) ≠ []) :
    volSol (atomSet atoms) (pruneForm atoms φ) = volSol (atomSet atoms) φ := by
  unfold volSol
  rw [sol_pruneForm atoms hφ hne,
    ← volume_sol_eq_volume_biUnion_nondegenCubes atoms (toDNFd_isDNFOf φ)]

/-! ## The two obligations, packaged against `hpos` -/

/-- `hbdd` at the pruned formula, from the user's `hbdd` at `φ`.

No longer on the chain: `Ttc.isBounded_sol_pruneForm_of_volSol_pos` (`Exec/BddFromPos`)
proves the same conclusion from `hφ` and `hpos` alone, and that is what
`Ttc.ttc_volume_api` passes.  Kept as the left-hand side of the drop-in check
`Ttc.pruneBdd_eq_isBounded_sol_pruneForm_of_volSol_pos`. -/
theorem pruneBdd (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))
    (hpos : 0 < volSol (atomSet atoms) φ) :
    Bornology.IsBounded (sol (atomSet atoms) (pruneForm atoms φ)) :=
  isBounded_sol_pruneForm atoms hφ (pruneNeNil atoms hpos) hbdd

/-- `hint` at the pruned formula, from `hpos`. -/
theorem pruneInt (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) :
    ∀ i : {c : Cube A // c ∈ toDNFd (pruneForm atoms φ)},
      (interior (region (atomSet atoms) i.val)).Nonempty :=
  interior_nonempty_pruneForm atoms hφ (pruneNeNil atoms hpos)

/-! ## The headline with `hint` traded for `hpos` -/

/-- **`thm:volumettc` with `hint` replaced by `0 < Vol(F)`.**

`Ttc.ttc_volume_cleanInput` run on `Ttc.pruneForm atoms φ` instead of `φ`.  The
degeneracy hypothesis is gone and what replaces it is strictly weaker: `hint` is not
derivable (`Ttc.hint_not_derivable`) but it is *made true* by pruning, and `hpos` is
spent only on `Ttc.pruneNeNil`.

**`hbdd` is at the pruned formula.**  This module only ever needs `Sol` of
`Ttc.pruneForm atoms φ` to be bounded, so that — and not boundedness of the user's
own `Sol(F)` — is what the binder asks for.  `Ttc.pruneBdd` supplies it from the
user's `hbdd`; `Ttc.isBounded_sol_pruneForm_of_volSol_pos` (`Exec/BddFromPos`,
downstream of this file) supplies it from `hφ` and `hpos` alone, which is what
`Ttc.ttc_volume_api` (`Exec/Api`) passes — so no boundedness hypothesis survives
into the headline.

Every mention of the formula in the conclusion is at the pruned formula — that is
what the algorithm is handed — except the accuracy target, which is the **original**
`volSol (atomSet atoms) φ`; the two agree by `Ttc.volSol_pruneForm`, the pruned
cubes being null.  `Ttc.sol` itself is *not* preserved, only measured. -/
theorem ttc_volume_prune
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) (pruneForm atoms φ)))
    (hpos : 0 < volSol (atomSet atoms) φ) :
    (1 - δ ≤
      (∫⁻ c, trajLaw
            (runRates
              (scaledAtoms atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                (autoGamma atoms (cleanForm atoms (pruneForm atoms φ))))
              (cleanForm atoms (pruneForm atoms φ)) ε δ
              (fun i =>
                runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                        (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
                  • autoCen atoms (cleanForm atoms (pruneForm atoms φ)) i)
              (runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                      (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
                  * autoGamma atoms (cleanForm atoms (pruneForm atoms φ))) c)
          {t | ttcRunOutput
                (scaledAtoms atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                  (autoGamma atoms (cleanForm atoms (pruneForm atoms φ))))
                (cleanForm atoms (pruneForm atoms φ)) ε δ
                (fun i =>
                  runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                          (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
                    • autoCen atoms (cleanForm atoms (pruneForm atoms φ)) i)
                (runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                        (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
                    * autoGamma atoms (cleanForm atoms (pruneForm atoms φ))) c t
              /
                (runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                  (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))) ^ n
            ∈ relErr ε (volSol (atomSet atoms) φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (runCount
          (scaledAtoms atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
            (autoGamma atoms (cleanForm atoms (pruneForm atoms φ))))
          (cleanForm atoms (pruneForm atoms φ)) ε δ
          (runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
              * autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) =
        (inputParamsTotal atoms (cleanForm atoms (pruneForm atoms φ)) ε δ).thresh →
      Terminates
          (inputParamsTotal atoms (cleanForm atoms (pruneForm atoms φ)) ε δ)
          (runOracles
            (scaledAtoms atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
              (autoGamma atoms (cleanForm atoms (pruneForm atoms φ))))
            (cleanForm atoms (pruneForm atoms φ)) ε δ
            (fun i =>
              runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                      (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
                • autoCen atoms (cleanForm atoms (pruneForm atoms φ)) i)
            (runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                    (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
                * autoGamma atoms (cleanForm atoms (pruneForm atoms φ))) c t)
                (toDNFd (cleanForm atoms (pruneForm atoms φ))) →
      runCost
          (inputParamsTotal atoms (cleanForm atoms (pruneForm atoms φ)) ε δ)
          (runOracles
            (scaledAtoms atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
              (autoGamma atoms (cleanForm atoms (pruneForm atoms φ))))
            (cleanForm atoms (pruneForm atoms φ)) ε δ
            (fun i =>
              runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                      (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
                • autoCen atoms (cleanForm atoms (pruneForm atoms φ)) i)
            (runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                    (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
                * autoGamma atoms (cleanForm atoms (pruneForm atoms φ))) c t)
          cVol cSample
          (runPrec
            (scaledAtoms atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
              (autoGamma atoms (cleanForm atoms (pruneForm atoms φ))))
            (cleanForm atoms (pruneForm atoms φ)) ε δ
            (runScale atoms (cleanForm atoms (pruneForm atoms φ)) ε δ
                    (autoGamma atoms (cleanForm atoms (pruneForm atoms φ)))
                * autoGamma atoms (cleanForm atoms (pruneForm atoms φ))))
                (toDNFd (cleanForm atoms (pruneForm atoms φ)))
        ≤ (toDNFd (cleanForm atoms (pruneForm atoms φ))).length * (cVol + cSample * thr)) := by
  have h := ttc_volume_cleanInput atoms (pruneForm atoms φ) ε δ hε0 hε1 hδ0 hδ1 hn
    (isPositive_pruneForm atoms φ) hbdd (pruneInt atoms hφ hpos)
  rwa [volSol_pruneForm atoms hφ (pruneNeNil atoms hpos)] at h

end Prune

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.pruneForm
#print axioms Ttc.isPositive_pruneForm
#print axioms Ttc.isPositive_nondegenCubes
#print axioms Ttc.nondegenCubes_ne_nil_of_volSol_pos
#print axioms Ttc.pruneNeNil
#print axioms Ttc.volSol_pos_of_interior
#print axioms Ttc.isDNFOf_pruneForm
#print axioms Ttc.toDNF_pruneForm
#print axioms Ttc.mem_toDNFd_pruneForm
#print axioms Ttc.interior_nonempty_pruneForm
#print axioms Ttc.sol_pruneForm
#print axioms Ttc.sol_pruneForm_subset
#print axioms Ttc.isBounded_sol_pruneForm
#print axioms Ttc.volSol_pruneForm
#print axioms Ttc.pruneBdd
#print axioms Ttc.pruneInt
#print axioms Ttc.ttc_volume_prune
