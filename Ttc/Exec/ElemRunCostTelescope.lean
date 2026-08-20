/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Runtime
import Ttc.Findings.SmallBody

/-!
# The two standing charges telescope

`Ttc.cubeCost_le` bounds four of the six elementary charges of one iteration outright and
leaves two standing — the thinning coins `Ttc.thinPassCost` and the overflow pass count
`j - j₁` — "because neither has a deterministic bound".  `Ttc.elemRunCost_le` then takes
each as a per-cube constant, `Cthin` and `Cpass`, which nothing supplies.

This file removes both.

`Ttc.step` passes `Ttc.stepPre`'s exit level through unchanged, so cube `i+1`'s entry
level *is* cube `i`'s exit level and the sum of the per-cube level increments telescopes to
the final level.  Both standing charges are bounded by that increment:

* `thinPassCost O j₀ j X ≤ (j - j₀) · |X| ≤ (j - j₀) · thr`  (`Ttc.card_thin_le`)
* `j - j₁ ≤ j - j₀`                                          (`Ttc.le_haltLevel`)

so together they cost `(thr + 1) · (j - j₀)` per cube and `(thr + 1) · finalLevel` overall.
No `Cthin`, no `Cpass`, and nothing about the pass count.
-/

namespace Ttc.ElemRunCostTelescope

open Ttc Multiset

variable {n : ℕ} {ι : Type*} (P : Params) (O : Oracles n ι)

/-- Each pass thins a sketch no larger than the one it started from. -/
theorem thinPassCost_le_mul (j₀ j : ℕ) (X : Multiset (Space n)) :
    thinPassCost O j₀ j X ≤ (j - j₀) * Multiset.card X := by
  unfold thinPassCost
  calc ∑ k ∈ Finset.Ico j₀ j, thinCost (O.thin j₀ k X)
      ≤ ∑ k ∈ Finset.Ico j₀ j, Multiset.card X :=
        Finset.sum_le_sum fun k _ ↦ card_thin_le O j₀ k X
    _ = (j - j₀) * Multiset.card X := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]

/-- The two standing charges of one cube, in terms of its level increment. -/
theorem standing_le (r Q Tw thr : ℕ) (st : SketchState n) (i : ι)
    (hX : Multiset.card (dropCovered O i st.X) ≤ thr) :
    thinPassCost O st.level (stepPre P O st i).1.level (dropCovered O i st.X)
        + ((stepPre P O st i).1.level - haltLevel P (O.vol i) st.level)
      ≤ (thr + 1) * ((stepPre P O st i).1.level - st.level) := by
  have hthin := thinPassCost_le_mul O st.level (stepPre P O st i).1.level
    (dropCovered O i st.X)
  have hthin' : thinPassCost O st.level (stepPre P O st i).1.level (dropCovered O i st.X)
      ≤ ((stepPre P O st i).1.level - st.level) * thr :=
    le_trans hthin (Nat.mul_le_mul_left _ hX)
  have hhalt : st.level ≤ haltLevel P (O.vol i) st.level := le_haltLevel P _ _
  have hpass : (stepPre P O st i).1.level - haltLevel P (O.vol i) st.level
      ≤ (stepPre P O st i).1.level - st.level := Nat.sub_le_sub_left hhalt _
  have : ((stepPre P O st i).1.level - st.level) * thr
      + ((stepPre P O st i).1.level - st.level)
      = (thr + 1) * ((stepPre P O st i).1.level - st.level) := by ring
  omega

/-- **`B`'s pointwise half.**  `Ttc.elemRunCost_le` without `Cthin` and `Cpass`: the two
charges they stood for are paid by the final level instead, and the pass count is never
bounded because it never has to be. -/
theorem elemRunCost_le_telescope (r Q Tw thr : ℕ) (ρ : ℤ) (cubes : List ι)
    (hT : 0 ≤ P.thresh) (hthr : P.thresh ≤ (thr : ℝ)) (h : Terminates P O cubes) :
    elemRunCost P O r Q Tw ρ cubes
      ≤ cubes.length * (n * r * Q + n * r * thr + 1 + thr * (Tw * (n * r)))
        + (thr + 1) * (cubes.foldl (step P O ρ) ⟨0, 0⟩).level := by
  set A := n * r * Q + n * r * thr + 1 + thr * (Tw * (n * r)) with hA
  have key : ∀ (l : List ι), (∀ (st : SketchState n) (i : ι), i ∈ l →
        AbsorbExits P O i (O.vol i) (dropCovered O i st.X) st.level
          (haltLevel P (O.vol i) st.level)) →
      ∀ (st : SketchState n) (acc : ℕ), (card st.X : ℝ) ≤ P.thresh →
      (l.foldl (fun (a : ℕ × SketchState n) i =>
          (a.1 + elemStepCost P O r Q Tw a.2 i, step P O ρ a.2 i)) (acc, st)).1
        ≤ acc + l.length * A
            + (thr + 1) * ((l.foldl (step P O ρ) st).level - st.level) := by
    intro l
    induction l with
    | nil => intro _ st acc _; simp
    | cons i rest ih =>
        intro hmem st acc hst
        have hi := hmem st i List.mem_cons_self
        have hXcard : card (dropCovered O i st.X) ≤ thr := by
          have h1 : card (dropCovered O i st.X) ≤ card st.X := card_dropCovered_le O i st.X
          have h2 : (card st.X : ℝ) ≤ (thr : ℝ) := le_trans hst hthr
          have : card st.X ≤ thr := by exact_mod_cast h2
          omega
        have hN : (stepPre P O st i).2 ≤ thr := by
          have h1 := stepPre_snd_le P O st i hi
          have : ((stepPre P O st i).2 : ℝ) ≤ (thr : ℝ) := le_trans h1 hthr
          exact_mod_cast this
        -- one cube: the bounded charges, plus the level increment
        have hstep : elemStepCost P O r Q Tw st i
            ≤ A + (thr + 1) * ((stepPre P O st i).1.level - st.level) := by
          rw [hA]
          have hc := cubeCost_le O r (dropCovered O i st.X) st.level
            (haltLevel P (O.vol i) st.level) (stepPre P O st i).1.level
            (stepPre P O st i).2 Q Tw thr hXcard hN
          have hs := standing_le P O r Q Tw thr st i hXcard
          calc elemStepCost P O r Q Tw st i
              ≤ n * r * Q + n * r * thr
                  + thinPassCost O st.level (stepPre P O st i).1.level
                      (dropCovered O i st.X)
                  + 1 + ((stepPre P O st i).1.level
                      - haltLevel P (O.vol i) st.level)
                  + thr * (Tw * (n * r)) := hc
            _ ≤ n * r * Q + n * r * thr + 1 + thr * (Tw * (n * r))
                  + (thr + 1) * ((stepPre P O st i).1.level - st.level) := by omega
        have hnext : (card (step P O ρ st i).X : ℝ) ≤ P.thresh :=
          card_step_le_thresh P O ρ st i hi
        have hrec := ih (fun st' i' hi' => hmem st' i' (List.mem_cons_of_mem _ hi'))
          (step P O ρ st i) (acc + elemStepCost P O r Q Tw st i) hnext
        simp only [List.foldl_cons, List.length_cons]
        refine le_trans hrec ?_
        -- the increments telescope: st.level ≤ (step …).level ≤ final level
        have hlev1 : st.level ≤ (step P O ρ st i).level := le_step_level P O ρ st i
        have hlev2 : (step P O ρ st i).level
            ≤ (rest.foldl (step P O ρ) (step P O ρ st i)).level :=
          Ttc.SmallBody.level_le_foldl_step P O ρ rest _
        have hsame : (step P O ρ st i).level = (stepPre P O st i).1.level := rfl
        have hAmul : (rest.length + 1) * A = A + rest.length * A := by ring
        -- the two level increments add up, so their `(thr+1)` multiples do too
        have hd : ((step P O ρ st i).level - st.level)
            + ((rest.foldl (step P O ρ) (step P O ρ st i)).level
                - (step P O ρ st i).level)
            = (rest.foldl (step P O ρ) (step P O ρ st i)).level - st.level := by omega
        have hdist : (thr + 1) * ((step P O ρ st i).level - st.level)
            + (thr + 1) * ((rest.foldl (step P O ρ) (step P O ρ st i)).level
                - (step P O ρ st i).level)
            = (thr + 1) * ((rest.foldl (step P O ρ) (step P O ρ st i)).level
                - st.level) := by
          rw [← Nat.left_distrib, hd]
        rw [← hsame] at hstep
        omega
  have hstart : ((card (⟨0, 0⟩ : SketchState n).X : ℝ)) ≤ P.thresh := by simpa using hT
  have := key cubes h ⟨0, 0⟩ 0 hstart
  simpa [elemRunCost] using this

#print axioms thinPassCost_le_mul
#print axioms standing_le
#print axioms elemRunCost_le_telescope

end Ttc.ElemRunCostTelescope
