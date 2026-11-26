/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Final

/-!
# Counting operations on a tree

`maxOps p` bounds the operations of every run of `p` (`exec_ops_le_maxOps`); it composes
through binds (`maxOps_bind_le`), restricted to the results a tree can give (`Post`).
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {d : ℕ} {α β γ : Type}

/-- **The most operations any run of `p` spends.** -/
def maxOps : Tree d α → ℕ∞
  | .pure _ => 0
  | .fail => 0
  | .step c k => opsTotal c.cost + maxOps (k c.val)
  | .coin k => 1 + ⨆ x, maxOps (k x)
  | .unit k => 1 + ⨆ x, maxOps (k x)
  | .gaussian k => d + ⨆ x, maxOps (k x)
  | .poisson _ k => 1 + ⨆ x, maxOps (k x)
  | .binom _ k => 1 + ⨆ x, maxOps (k x)
  | .setBudget _ k => 1 + maxOps k
  | .spend k => ⨆ x, maxOps (k x)

/-- **Every run spends at most `maxOps`.** -/
theorem exec_ops_le_maxOps (p : Tree d α) (b : ℕ) (t : Tape d) :
    ((exec p b t).2.1 : ℕ∞) ≤ maxOps p := by
  induction p generalizing b t with
  | pure a => simp [exec, maxOps]
  | fail => simp [exec, maxOps]
  | step c k ih =>
      simp only [exec, maxOps, Nat.cast_add]
      exact add_le_add le_rfl (ih c.val b t)
  | coin k ih =>
      simp only [exec, maxOps, Nat.cast_add, Nat.cast_one]
      exact add_le_add le_rfl ((ih _ b _).trans (le_iSup (fun x => maxOps (k x)) _))
  | unit k ih =>
      simp only [exec, maxOps, Nat.cast_add, Nat.cast_one]
      exact add_le_add le_rfl ((ih _ b _).trans (le_iSup (fun x => maxOps (k x)) _))
  | gaussian k ih =>
      simp only [exec, maxOps, Nat.cast_add]
      exact add_le_add le_rfl ((ih _ b _).trans (le_iSup (fun x => maxOps (k x)) _))
  | poisson r k ih =>
      simp only [exec, maxOps, Nat.cast_add, Nat.cast_one]
      exact add_le_add le_rfl ((ih _ b _).trans (le_iSup (fun x => maxOps (k x)) _))
  | binom N k ih =>
      simp only [exec, maxOps, Nat.cast_add, Nat.cast_one]
      exact add_le_add le_rfl ((ih _ b _).trans (le_iSup (fun x => maxOps (k x)) _))
  | setBudget c k ih =>
      simp only [exec, maxOps, Nat.cast_add, Nat.cast_one]
      exact add_le_add le_rfl (ih _ _)
  | spend k ih =>
      cases b with
      | zero => exact (ih _ 0 t).trans (le_iSup (fun x => maxOps (k x)) _)
      | succ b => exact (ih _ b t).trans (le_iSup (fun x => maxOps (k x)) _)

/-- **A sequence spends at most the first part's most, plus the most of the continuation at
any result the first part can give.** -/
theorem maxOps_bind_le {p : Tree d α} {f : α → Tree d β} {Q : α → Prop} (hp : Post p Q)
    (B : ℕ∞) (hf : ∀ a, Q a → maxOps (f a) ≤ B) : maxOps (p.bind f) ≤ maxOps p + B := by
  induction p with
  | pure a =>
      show maxOps (f a) ≤ 0 + B
      rw [zero_add]; exact hf a hp
  | fail => exact bot_le
  | step c k ih =>
      show opsTotal c.cost + maxOps ((k c.val).bind f) ≤ opsTotal c.cost + maxOps (k c.val) + B
      rw [add_assoc]; exact add_le_add le_rfl (ih c.val hp)
  | coin k ih =>
      show 1 + ⨆ x, maxOps ((k x).bind f) ≤ 1 + (⨆ x, maxOps (k x)) + B
      rw [add_assoc]
      refine add_le_add le_rfl (iSup_le fun x => (ih x (hp x)).trans ?_)
      exact add_le_add (le_iSup (fun x => maxOps (k x)) x) le_rfl
  | unit k ih =>
      show 1 + ⨆ x, maxOps ((k x).bind f) ≤ 1 + (⨆ x, maxOps (k x)) + B
      rw [add_assoc]
      refine add_le_add le_rfl (iSup_le fun x => (ih x (hp x)).trans ?_)
      exact add_le_add (le_iSup (fun x => maxOps (k x)) x) le_rfl
  | gaussian k ih =>
      show d + ⨆ x, maxOps ((k x).bind f) ≤ d + (⨆ x, maxOps (k x)) + B
      rw [add_assoc]
      refine add_le_add le_rfl (iSup_le fun x => (ih x (hp x)).trans ?_)
      exact add_le_add (le_iSup (fun x => maxOps (k x)) x) le_rfl
  | poisson r k ih =>
      show 1 + ⨆ x, maxOps ((k x).bind f) ≤ 1 + (⨆ x, maxOps (k x)) + B
      rw [add_assoc]
      refine add_le_add le_rfl (iSup_le fun x => (ih x (hp x)).trans ?_)
      exact add_le_add (le_iSup (fun x => maxOps (k x)) x) le_rfl
  | binom N k ih =>
      show 1 + ⨆ x, maxOps ((k x).bind f) ≤ 1 + (⨆ x, maxOps (k x)) + B
      rw [add_assoc]
      refine add_le_add le_rfl (iSup_le fun x => (ih x (hp x)).trans ?_)
      exact add_le_add (le_iSup (fun x => maxOps (k x)) x) le_rfl
  | setBudget c k ih =>
      show 1 + maxOps (k.bind f) ≤ 1 + maxOps k + B
      rw [add_assoc]; exact add_le_add le_rfl (ih hp)
  | spend k ih =>
      show ⨆ x, maxOps ((k x).bind f) ≤ (⨆ x, maxOps (k x)) + B
      refine iSup_le fun x => (ih x (hp x)).trans ?_
      exact add_le_add (le_iSup (fun x => maxOps (k x)) x) le_rfl

theorem maxOps_compute (c : Prog α) : maxOps (compute (n := d) c) = opsTotal c.cost := by
  show (opsTotal c.cost : ℕ∞) + 0 = _
  rw [add_zero]

theorem maxOps_pure (a : α) : maxOps (Tree.pure (n := d) a) = 0 := rfl

/-- `k` rounds of a loop spend at most `k` times a body's most. -/
theorem maxOps_loopRounds {body : β → Tree d (β ⊕ γ)} {B : ℕ∞} (hb : ∀ y, maxOps (body y) ≤ B) :
    ∀ (k : ℕ) (y : β), maxOps (loopRounds body k y) ≤ k * B
  | 0, y => by simp [loopRounds, maxOps]
  | k + 1, y => by
      refine (maxOps_bind_le (post_of_forall (Q := fun _ => True) (fun _ => trivial) _) (k * B)
        fun r _ => ?_).trans ?_
      · rcases r with y' | c
        · exact maxOps_loopRounds hb k y'
        · exact bot_le
      · calc maxOps (body y) + k * B ≤ B + k * B := add_le_add (hb y) le_rfl
          _ = ((k + 1 : ℕ) : ℕ∞) * B := by push_cast; ring

end ttc.Tape
