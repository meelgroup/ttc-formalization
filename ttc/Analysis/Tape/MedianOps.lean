/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.ArithmeticOps
import ttc.Analysis.Tape.CV18Sim

/-! # Cost of the sealed list median -/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program

private def rankCheck (w : List (Num ℝ)) (one zero rank : Num ℕ) (x : Num ℝ) :
    Prog (Num ℝ × Bool) := do
  let fb ← w.mapM fun y => A.lt y x
  let below ← A.sumList (fb.map fun f => if f then one else zero)
  let fa ← w.mapM fun y => A.le y x
  let atMost ← A.sumList (fa.map fun f => if f then one else zero)
  let a ← A.le below rank
  let b ← A.lt rank atMost
  A.pure (x, a && b)

private theorem opsTotal_rankCheck_le (w : List (Num ℝ)) (one zero rank : Num ℕ) (x : Num ℝ) :
    opsTotal (rankCheck w one zero rank x).cost ≤ 4 * w.length + 4 := by
  have hb := opsTotal_mapM_le 1 (fun y => A.lt y x) (fun y => (opsTotal_lt y x).le) w
  have ha := opsTotal_mapM_le 1 (fun y => A.le y x) (fun y => (opsTotal_le y x).le) w
  have sb := opsTotal_sumList_le
    ((w.mapM fun y => A.lt y x).val.map fun f => if f then one else zero)
  have sa := opsTotal_sumList_le
    ((w.mapM fun y => A.le y x).val.map fun f => if f then one else zero)
  simp only [mul_one] at hb ha
  simp only [List.length_map, val_mapM] at sb sa
  simp only [rankCheck, opsTotal_bind, opsTotal_pure, opsTotal_le, opsTotal_lt, add_zero]
  rw [← val_mapM (fun y => A.lt y x)] at sb
  rw [← val_mapM (fun y => A.le y x)] at sa
  omega

/-- The sealed median includes the initial list reads, every rank count and
comparison, and the possible fallback literal. -/
theorem opsTotal_median_le (m : Num ℕ) (v : List (Num ℝ)) :
    opsTotal (A.median m v).cost ≤ v.length * (4 * v.length + 5) + 5 := by
  let w := (v.mapM A.cell).val
  let one := (A.lit (1 : ℕ)).val
  let zero := (A.lit (0 : ℕ)).val
  let rank := (A.div m (A.lit (2 : ℕ)).val).val
  have hw : w.length = v.length := by rw [show w = (v.mapM A.cell).val from rfl, val_mapM, List.length_map]
  have hv := opsTotal_mapM_le 1 A.cell (fun x : Num ℝ => (opsTotal_cell x).le) v
  have hp := opsTotal_mapM_le (4 * w.length + 4) (rankCheck w one zero rank)
    (opsTotal_rankCheck_le w one zero rank) w
  have hfirst := opsTotal_firstPassing_le (w.mapM (rankCheck w one zero rank)).val
  simp only [mul_one] at hv
  simp only [A.median, opsTotal_bind, opsTotal_lit, opsTotal_div]
  change opsTotal (v.mapM A.cell).cost +
    (1 + (1 + (1 + (1 + (opsTotal (w.mapM (rankCheck w one zero rank)).cost +
      opsTotal (A.firstPassing (w.mapM (rankCheck w one zero rank)).val).cost))))) ≤ _
  have hmul : w.length * (4 * w.length + 4) + v.length =
      v.length * (4 * v.length + 5) := by rw [hw]; ring
  omega

end ttc.Tape
