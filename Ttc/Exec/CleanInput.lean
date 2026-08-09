/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Rescaled
import Ttc.Exec.Cleanup

/-!
# `Exec/CleanInput`: `hcoeff` discharged by running on the cleaned formula

`Ttc.ttc_volume_full` (`Exec/Rescaled`) still carries

```
hcoeff : ∀ j : FacetIndex (toDNFd φ), (atoms j.2.val.atom).coeff ≠ 0
```

— *no facet of the DNF has a zero normal vector*.  `Exec/Cleanup` builds, for any
positive `φ` with a nonempty solution set, a positive formula
`Ttc.cleanForm atoms φ` for which that hypothesis holds outright
(`Ttc.coeff_ne_zero_toDNFd_cleanForm`).  This module runs the headline **on that
formula** and so drops the binder: `Ttc.ttc_volume_cleanInput` has twelve
hypotheses where `Ttc.ttc_volume_full` has thirteen, and nothing is added.

## This is a sound preprocessing pass, not a change of problem

`Ttc.sol_cleanForm` is an equality of **sets**:

```
sol (atomSet atoms) (cleanForm atoms φ) = sol (atomSet atoms) φ
```

The body being measured is literally unchanged, so `Ttc.volSol` is unchanged
(`Ttc.volSol_cleanForm`) and the conclusion's accuracy conjunct is stated about the
**original** `volSol (atomSet atoms) φ`, with no post-processing of the estimate.

Contrast the dilation of `Exec/Rescaled.lean`, which discharges `hvol` by scaling the
input by `c = Ttc.runScale …`: there `Sol(F)` genuinely *moves* to `c · Sol(F)`, and
the estimate has to be divided by `cⁿ` to come back.  Here nothing moves; only the
*description* of the body — the list of polytopes handed to the algorithm — changes,
by deleting literals that denote `Set.univ` and cubes that denote `∅`.

## Why the formula has to move with the DNF

One could hope to clean the DNF in place and leave `φ` alone, but
`Ttc.IsDNFOf D φ` quantifies over **all** Boolean assignments, while the cleanup is
justified only at the assignments a point of `Space n` induces.
`Ttc.not_isDNFOf_cleanDNF` is the machine-checked refutation: for the single atom
`0 · x ≤ 1` over `A = Unit` and `φ = atom ()`, the cleaned DNF contains the empty
cube, which holds at `v = fun _ => False` where `φ` does not.  So the *formula* is
rebuilt from the cleaned cubes (`Ttc.cleanForm = dnfForm ∘ cleanDNF ∘ toDNFd`), which
is a genuine `Ttc.IsDNFOf` of itself (`Ttc.isDNFOf_dnfForm`) and has the same
solution set.

## The one real step

`Ttc.sol_cleanForm` and its companions need `cleanDNF atoms (toDNFd φ) ≠ []` — when
every cube is void the cleaned DNF is `[]`, `Sol(F) = ∅`, and there is no positive
formula left to run on.  That side condition is *already implied by the headline's
own binders*: `hint` says every cube of `toDNFd φ` has nonempty interior, and
`Ttc.toDNFd_ne_nil` says there is at least one cube, so `Sol(F)` is nonempty
(`Ttc.sol_nonempty_of_interior`) and `Ttc.cleanDNF_ne_nil_of_sol_nonempty` applies.
No hypothesis is added.
-/

namespace Ttc

open MeasureTheory Set Pointwise

section CleanInput

variable {A : Type*} {n : ℕ}

/-! ## `hint` implies a nonempty solution set -/

/-- **A full-dimensional decomposition has a nonempty solution set.**  `hφ` gives a
cube (`Ttc.toDNFd_ne_nil`), `hint` gives a point of its interior, `interior_subset`
puts that point in the cube's region, and `Ttc.region_subset_sol` puts it in `Sol(F)`.

This is the only genuine step needed to run `Ttc.ttc_volume_full` on the cleaned
formula: it turns the headline's own `hint` into the side condition
`Ttc.cleanDNF_ne_nil_of_sol_nonempty` asks for. -/
theorem sol_nonempty_of_interior (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hint : ∀ i : {c : Cube A // c ∈ toDNFd φ},
      (interior (region (atomSet atoms) i.val)).Nonempty) :
    (sol (atomSet atoms) φ).Nonempty := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (toDNFd_ne_nil hφ)
  obtain ⟨x, hx⟩ := hint ⟨c, hc⟩
  exact ⟨x, region_subset_sol (toDNFd_isDNFOf φ) hc (interior_subset hx)⟩

/-- The side condition of `Exec/Cleanup`'s formula-level results, discharged from the
headline's binders alone. -/
theorem cleanDNF_ne_nil_of_interior (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hint : ∀ i : {c : Cube A // c ∈ toDNFd φ},
      (interior (region (atomSet atoms) i.val)).Nonempty) :
    cleanDNF atoms (toDNFd φ) ≠ [] :=
  cleanDNF_ne_nil_of_sol_nonempty atoms (toDNFd_isDNFOf φ) (toDNFd_isPositive hφ)
    (sol_nonempty_of_interior atoms hφ hint)

/-! ## The three hypotheses of the headline, transported to `cleanForm` -/

/-- **The volume is untouched by the cleanup** — `Ttc.volSol` is the measure of
`Ttc.sol`, and `Ttc.sol_cleanForm` is an equality of sets. -/
theorem volSol_cleanForm (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hne : cleanDNF atoms (toDNFd φ) ≠ []) :
    volSol (atomSet atoms) (cleanForm atoms φ) = volSol (atomSet atoms) φ := by
  unfold volSol
  rw [sol_cleanForm atoms hφ hne]

/-- **`hbdd` for the cleaned formula.**  Same set, so same boundedness. -/
theorem cleanBdd (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))
    (hint : ∀ i : {c : Cube A // c ∈ toDNFd φ},
      (interior (region (atomSet atoms) i.val)).Nonempty) :
    Bornology.IsBounded (sol (atomSet atoms) (cleanForm atoms φ)) := by
  rw [sol_cleanForm atoms hφ (cleanDNF_ne_nil_of_interior atoms hφ hint)]
  exact hbdd

/-- **`hint` for the cleaned formula.**  Every cleaned cube's region *equals* some
original cube's region (`Ttc.region_cleanDNF_eq`), so full-dimensionality transports
along that equality — the cleanup deletes only literals denoting `Set.univ`. -/
theorem cleanInt (atoms : A → LinAtom n) {φ : BForm A} (hφ : φ.IsPositive)
    (hint : ∀ i : {c : Cube A // c ∈ toDNFd φ},
      (interior (region (atomSet atoms) i.val)).Nonempty) :
    ∀ i : {c : Cube A // c ∈ toDNFd (cleanForm atoms φ)},
      (interior (region (atomSet atoms) i.val)).Nonempty := by
  rintro ⟨c, hc⟩
  show (interior (region (atomSet atoms) c)).Nonempty
  have hc' : c ∈ cleanDNF atoms (toDNFd φ) :=
    (mem_toDNFd_cleanForm atoms hφ (cleanDNF_ne_nil_of_interior atoms hφ hint)).1 hc
  obtain ⟨c₀, hc₀, heq⟩ := region_cleanDNF_eq atoms (toDNFd_isPositive hφ) hc'
  rw [heq]
  exact hint ⟨c₀, hc₀⟩

/-! ## The headline with `hcoeff` discharged -/

/-- **`thm:volumettc` at 12 binders: no oracle, no precision, no parameter block, no
volume hypothesis, no inscribed-ball data and no degeneracy hypothesis.**

`Ttc.ttc_volume_full` run on `Ttc.cleanForm atoms φ` instead of `φ`.  Every mention of
the formula in the conclusion is at the cleaned formula — that *is* what the algorithm
is handed — except the accuracy target, which is the **original**
`volSol (atomSet atoms) φ`; the two are equal because `Ttc.sol_cleanForm` is an
equality of sets (`Ttc.volSol_cleanForm`).

`hcoeff` is gone and nothing replaces it: the four obligations at the cleaned formula
are `Ttc.isPositive_cleanForm` (unconditional), `Ttc.cleanBdd`, `Ttc.cleanInt` and
`Ttc.coeff_ne_zero_toDNFd_cleanForm`, the last of which needs only `hφ` and
`Ttc.cleanDNF_ne_nil_of_interior`. -/
theorem ttc_volume_cleanInput
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
        ≤ (toDNFd (cleanForm atoms φ)).length * (cVol + cSample * thr)) := by
  have hne : cleanDNF atoms (toDNFd φ) ≠ [] := cleanDNF_ne_nil_of_interior atoms hφ hint
  have h := ttc_volume_full atoms (cleanForm atoms φ) ε δ hε0 hε1 hn
    (isPositive_cleanForm atoms φ) (cleanBdd atoms hφ hbdd hint) hδ0 hδ1
    (coeff_ne_zero_toDNFd_cleanForm atoms hφ hne) (cleanInt atoms hφ hint)
  rwa [volSol_cleanForm atoms hφ hne] at h

/-- **`thm:runtime` for the same run** — the cost conjunct of
`Ttc.ttc_volume_cleanInput`, at twelve binders. -/
theorem ttc_volume_cleanInput_cost
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (hφ : φ.IsPositive)
    (hbdd : Bornology.IsBounded (sol (atomSet atoms) φ))
    (hint : ∀ i : {c : Cube A // c ∈ toDNFd φ},
      (interior (region (atomSet atoms) i.val)).Nonempty) :
    ∀ (c : ℕ → Space n)
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
        ≤ (toDNFd (cleanForm atoms φ)).length * (cVol + cSample * thr) :=
  (ttc_volume_cleanInput atoms φ ε δ hε0 hε1 hδ0 hδ1 hn hφ hbdd hint).2

end CleanInput

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.sol_nonempty_of_interior
#print axioms Ttc.cleanDNF_ne_nil_of_interior
#print axioms Ttc.volSol_cleanForm
#print axioms Ttc.cleanBdd
#print axioms Ttc.cleanInt
#print axioms Ttc.ttc_volume_cleanInput
#print axioms Ttc.ttc_volume_cleanInput_cost
