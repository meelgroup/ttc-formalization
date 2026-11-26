/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Ops
import ttc.Analysis.Tape.ArithmeticOps

/-! # Operation bounds for the sealed deletion and thinning scans -/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {d : ℕ}

theorem maxOps_filterStep_le {keep : (Fin d → Num ℤ) → Tree d Bool} (B : ℕ∞)
    (hB : ∀ x, maxOps (keep x) ≤ B) (one : Num ℕ)
    (acc : List (Fin d → Num ℤ) × Num ℕ) (x : Fin d → Num ℤ) :
    maxOps (filterStep keep one acc x) ≤ B + 3 := by
  rw [filterStep, maxOps_compute_bind, opsTotal_cell, Nat.cast_one]
  let f : Bool → Tree d (List (Fin d → Num ℤ) × Num ℕ) := fun k =>
    if k then
      (compute (A.push acc.1 (A.cell x).val)).bind fun ys =>
        (compute (A.add acc.2 one)).bind fun c => Tree.pure (ys, c)
    else Tree.pure acc
  have hf : ∀ k, maxOps (f k) ≤ 2 := by
    intro k
    cases k <;> norm_num [f, maxOps_compute_bind, maxOps]
  have h := maxOps_bind_le (p := keep (A.cell x).val) (f := f)
    (post_of_forall (Q := fun _ : Bool => True) (fun _ => trivial) _)
    2 (fun k _ => hf k)
  calc _ ≤ 1 + (maxOps (keep (A.cell x).val) + 2) := add_le_add le_rfl h
    _ ≤ 1 + (B + 2) := add_le_add le_rfl (add_le_add (hB _) le_rfl)
    _ = B + 3 := by ring

/-- One literal each for zero and one, then at most one read, one test, one
append and one increment per copy. -/
theorem maxOps_filterCopiesT_le {keep : (Fin d → Num ℤ) → Tree d Bool}
    (B : ℕ∞) (hB : ∀ x, maxOps (keep x) ≤ B) (X : List (Fin d → Num ℤ)) :
    maxOps (filterCopiesT keep X) ≤ 2 + X.length * (B + 3) := by
  rw [filterCopiesT_eq]
  simp only [maxOps, opsTotal_lit, Nat.cast_one, ← add_assoc]
  exact add_le_add le_rfl (maxOps_foldlM_le _ _ (fun acc x => maxOps_filterStep_le B hB _ acc x) X _)

theorem maxOps_filterCopiesT_coin_le (X : List (Fin d → Num ℤ)) :
    maxOps (filterCopiesT (d := d) (fun _ => coinT) X) ≤ 2 + X.length * 4 := by
  apply maxOps_filterCopiesT_le 1
  intro x
  simp [coinT, maxOps]

private theorem post_filterFoldl_size (keep : (Fin d → Num ℤ) → Tree d Bool) (one : Num ℕ) :
    ∀ (xs : List (Fin d → Num ℤ)) (a : List (Fin d → Num ℤ) × Num ℕ),
      Post (xs.foldlM (filterStep keep one) a) fun r => r.1.length ≤ a.1.length + xs.length
  | [], _ => by simp [List.foldlM, Post]
  | x :: xs, a => by
      rw [List.foldlM_cons]
      have hstep : Post (filterStep keep one a x) (fun r => r.1.length ≤ a.1.length + 1) := by
        unfold filterStep
        refine post_compute_bind (Post.bind (post_of_forall (fun k => ?_) _))
        cases k
        · exact Nat.le_succ _
        · refine post_compute_bind (post_compute_bind ?_)
          change (A.push a.1 (A.cell x).val).val.length ≤ a.1.length + 1
          simp [A.push, ttc.Model.Operations.push, Charged.val_op]
      refine Post.bind (hstep.mono fun a' ha' => (post_filterFoldl_size keep one xs a').mono
        fun r hr => ?_)
      simp only [List.length_cons]
      omega

/-- Copy scans only retain existing entries. -/
theorem post_filterCopiesT_size (keep : (Fin d → Num ℤ) → Tree d Bool) (X : List (Fin d → Num ℤ)) :
    Post (filterCopiesT keep X) fun r => r.1.length ≤ X.length := by
  rw [filterCopiesT_eq]
  change Post (X.foldlM (filterStep keep (A.lit (1 : ℕ)).val) ([], (A.lit (0 : ℕ)).val)) _
  simpa using post_filterFoldl_size keep (A.lit (1 : ℕ)).val X ([], (A.lit (0 : ℕ)).val)

end ttc.Tape
