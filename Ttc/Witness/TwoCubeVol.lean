/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Witness.Inputs

/-!
# `Witness/TwoCubeVol`: the two-cube witness satisfies the volume hypothesis

The headline theorem takes the regime condition in the transparent form

```
hvol : P.thresh / 4 ≤ volSol (atomSet atoms) φ
```

— "the solution set is at least a quarter of the threshold" — rather than the opaque
per-cube `big` binder; `Ttc.big_of_volume` (`Ttc/Exec/RegimeMain.lean`) recovers `big`
from it.  For the non-vacuity witness to survive that change, the **two-cube instance
of `Ttc/Witness/TwoCube.lean` must satisfy `hvol`**.  This file proves it, at every
`n ≥ 1` and every `(ε, δ) ∈ (0,1]²`.

## Why it holds

Not by accident: the witness **sizes its boxes at the threshold**.  The common side is
`Ttc.TwoCube.sideT = max 1 Thresh` (`Ttc/Witness/TwoCube.lean`), so each box has side
at least `1` *and* at least `Thresh`, hence volume `sideTⁿ ≥ sideT ≥ Thresh` once
`n ≥ 1`.  That is the same choice the paper's own examples make, and it is why the
two-cube instance is in the regime at all — an instance whose solution set were small
compared to `Thresh` would simply be outside the theorem's scope.

## The bound is one-sided

`volSol` here is the volume of the **union** of the two boxes, but no volume
additivity is needed: one box already clears `Thresh`, and `Ttc.region_subset_sol`
puts it inside `Sol(F)`, so `measure_mono` finishes.  In particular the disjointness
result `Ttc.TwoCube.sol_eq_union_two_T` is **not** used — this file would go through
verbatim for a single cube.  The only side condition is that `Sol(F)` has finite
volume, so that `ENNReal.toReal` is monotone across the inclusion; that is
`Ttc.TwoCube.isBounded_sol_T`.

## What is landed

| result | content |
| --- | --- |
| `Ttc.TwoCube.volume_sol_ne_top_T` | `Sol(F)` has finite volume — it is a union of two boxes |
| `Ttc.TwoCube.volume_region_le_volSol` | each cube's region has volume at most `Vol(Sol(F))` |
| `Ttc.TwoCube.thresh_le_volSol` | `Thresh ≤ Vol(Sol(F))`, the sharp form |
| `Ttc.TwoCube.two_cube_thresh_le_volSol` | `hvol` itself, on `Ttc.TwoCube.MTT` |
| `Ttc.TwoCube.two_cube_thresh_le_volSol_atomSet` | the same on `Ttc.atomSet (atomsT …)` |

The `δ`-hypotheses `hδ0 : 0 < δ`, `hδ1 : δ ≤ 1` are needed only for the last division
step (`Thresh / 4 ≤ Thresh` needs `0 ≤ Thresh`, which is
`Ttc.TwoCube.parT_thresh_pos`); `Ttc.TwoCube.thresh_le_volSol` is free of them.
-/

namespace Ttc

namespace TwoCube

open MeasureTheory

/-- **`Sol(F)` has finite volume.**  It is the union of two boxes of side
`Ttc.TwoCube.sideT`, hence bounded (`Ttc.TwoCube.isBounded_sol_T`). -/
theorem volume_sol_ne_top_T (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    volume (sol (MTT n hn ε δ hε0 hε1) (twoForm n)) ≠ ⊤ :=
  volume_ne_top_of_isBounded (isBounded_sol_T n hn ε δ hε0 hε1)

/-- **Each cube's region has volume at most `Vol(Sol(F))`.**  `thm:decomposition`'s
soundness half (`Ttc.region_subset_sol`) puts the region inside `Sol(F)`; monotonicity
of `ENNReal.toReal` across the inclusion needs the larger side finite, which is
`Ttc.TwoCube.volume_sol_ne_top_T`.

This is the whole use made of the two-cube structure: **one** cube suffices, so no
volume additivity — and hence no disjointness — is required. -/
theorem volume_region_le_volSol (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {i : Cube (A2 n)} (hi : i ∈ Ttc.toDNF (twoForm n)) :
    (volume (region (MTT n hn ε δ hε0 hε1) i)).toReal
      ≤ volSol (MTT n hn ε δ hε0 hε1) (twoForm n) := by
  rw [volSol]
  exact ENNReal.toReal_mono (volume_sol_ne_top_T n hn ε δ hε0 hε1)
    (measure_mono (region_subset_sol (toDNF_isDNFOf _) hi))

/-- **`Thresh ≤ Vol(Sol(F))` on the two-cube witness.**  The left box alone has volume
`sideTⁿ ≥ sideT ≥ Thresh` (`Ttc.TwoCube.thresh_le_volume_region`, which is where
`sideT = max 1 Thresh` pays off), and it sits inside `Sol(F)`.

This is the sharp form; `Ttc.TwoCube.two_cube_thresh_le_volSol` weakens it by the
factor `4` the headline asks for. -/
theorem thresh_le_volSol (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (parT n hn ε δ hε0 hε1).thresh ≤ volSol (MTT n hn ε δ hε0 hε1) (twoForm n) :=
  le_trans (thresh_le_volume_region n hn ε δ hε0 hε1 mem_toDNF_cubeL)
    (volume_region_le_volSol n hn ε δ hε0 hε1 mem_toDNF_cubeL)

/-- **The headline's `hvol`, on the two-cube witness.**  The solution set is at least a
quarter of the threshold — in fact at least the whole threshold
(`Ttc.TwoCube.thresh_le_volSol`), because the witness sizes its boxes at
`max 1 Thresh`.

`Ttc.big_of_volume` turns this into the `big` binder, so the non-vacuity witness
survives the replacement of the opaque regime binder by this transparent hypothesis. -/
theorem two_cube_thresh_le_volSol (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (parT n hn ε δ hε0 hε1).thresh / 4
      ≤ volSol (MTT n hn ε δ hε0 hε1) (twoForm n) := by
  have h := thresh_le_volSol n hn ε δ hε0 hε1
  have hp := parT_thresh_pos n hn ε δ hε0 hε1 hδ0 hδ1
  linarith

/-- **`hvol` in the shape the headline states it**, over `Ttc.atomSet` at the witness's
atom family.  `Ttc.TwoCube.atomSet_atomsT` identifies that with
`Ttc.TwoCube.MTT` definitionally, so this is
`Ttc.TwoCube.two_cube_thresh_le_volSol` transported along a `rfl`. -/
theorem two_cube_thresh_le_volSol_atomSet (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (parT n hn ε δ hε0 hε1).thresh / 4
      ≤ volSol (Ttc.atomSet (atomsT n hn ε δ hε0 hε1)) (twoForm n) := by
  rw [atomSet_atomsT]
  exact two_cube_thresh_le_volSol n hn ε δ hε0 hε1 hδ0 hδ1

end TwoCube

end Ttc

#print axioms Ttc.TwoCube.volume_sol_ne_top_T
#print axioms Ttc.TwoCube.volume_region_le_volSol
#print axioms Ttc.TwoCube.thresh_le_volSol
#print axioms Ttc.TwoCube.two_cube_thresh_le_volSol
#print axioms Ttc.TwoCube.two_cube_thresh_le_volSol_atomSet
