/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.ChargedExec

/-!
# What the charged CV18 program spends on a tape

The cost of a trace includes every tick and the cost of computing the answer
to each membership query that is actually made. The cap has the same semantics
as in `cexec`: an exhausted query is not answered, and the trace stops there.
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open ttc.Model.Operations (Tape)
open ttc.ChargedCV18 (ChargedProgram)
open ArlibCommunity.Algorithms.CV18 (AmbientSpace)

variable {d : ℕ} {α β : Type}

/-- Trace cost in the charged CV18 currency, with membership answered by computation. -/
def cexecOps (member : AmbientSpace d → ttc.ChargedCV18.Counted Bool) :
    ChargedProgram d α → ℕ∞ → Tape d → ℕ
  | .pure _, _, _ => 0
  | .query x k, b, t =>
      if b = 0 then 0 else (member x).cost + cexecOps member (k (member x).value) (b - 1) t
  | .randomNat _ k, b, t => cexecOps member (k 0) b t
  | .randomPoint _ _ k, b, t => cexecOps member (k (t 0).2.1) b t.tail
  | .randomReal _ _ k, b, t => cexecOps member (k (t 0).2.2) b t.tail
  | .tick c k, b, t => ttc.ChargedCV18.opsTotal c + cexecOps member k b t

variable (member : AmbientSpace d → ttc.ChargedCV18.Counted Bool)

/-- Sequencing sums the cost of the traces that are reached. -/
theorem cexecOps_bind (P : ChargedProgram d α) (f : α → ChargedProgram d β) (b : ℕ∞)
    (t : Tape d) :
    cexecOps member (P.bind f) b t = cexecOps member P b t +
      match cexec (fun x => (member x).value) P b t with
      | (none, _, _) => 0
      | (some a, b', t') => cexecOps member (f a) b' t' := by
  induction P generalizing b t with
  | pure a => simp [ChargedProgram.bind, cexec, cexecOps]
  | query x k ih =>
      simp only [ChargedProgram.bind, cexec, cexecOps]
      split_ifs
      · rfl
      · rw [ih, add_assoc]
  | randomNat law k ih => exact ih _ _ _
  | randomPoint law h k ih => exact ih _ _ _
  | randomReal law h k ih => exact ih _ _ _
  | tick c k ih =>
      simp only [ChargedProgram.bind, cexec, cexecOps, ih, add_assoc]

/-- Installing a finite cap in the syntax counts the same cost as setting that cap on the
tape interpreter. -/
theorem cexecOps_withQueryCap (P : ChargedProgram d α) (c : ℕ) (t : Tape d) :
    cexecOps member (P.withQueryCap c) ⊤ t = cexecOps member P c t := by
  induction P generalizing c t with
  | pure a => rfl
  | query x k ih =>
      cases c with
      | zero => rfl
      | succ c =>
          have hs : ((c + 1 : ℕ) : ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero c
          simp only [ChargedProgram.withQueryCap, cexecOps, ENat.top_ne_zero, ite_false,
            enat_top_sub_one, hs, enat_succ_sub_one, ih]
  | randomNat law k ih => exact ih _ c t
  | randomPoint law h k ih => exact ih _ c t.tail
  | randomReal law h k ih => exact ih _ c t.tail
  | tick ops k ih => simp only [ChargedProgram.withQueryCap, cexecOps, ih]

/-- The actual cost on every tape is bounded by the operation bound of the charged
program with all queries answered by the same charged membership test. -/
theorem cexecOps_le_opCost_answerWith (P : ChargedProgram d α) (b : ℕ∞) (t : Tape d) :
    (cexecOps member P b t : ℕ∞) ≤ (P.answerWith member).opCost := by
  induction P generalizing b t with
  | pure a => exact le_rfl
  | query x k ih =>
      by_cases hb : b = 0
      · simp [cexecOps, hb]
      · simp only [cexecOps, hb, ite_false, Nat.cast_add, ChargedProgram.answerWith,
          ChargedProgram.opCost]
        exact add_le_add le_rfl (ih _ _ _)
  | randomNat law k ih =>
      exact (ih 0 b t).trans (le_iSup (fun i => ((k i).answerWith member).opCost) 0)
  | randomPoint law h k ih =>
      exact (ih _ b t.tail).trans
        (le_iSup (fun x => ((k x).answerWith member).opCost) (t 0).2.1)
  | randomReal law h k ih =>
      exact (ih _ b t.tail).trans
        (le_iSup (fun x => ((k x).answerWith member).opCost) (t 0).2.2)
  | tick ops k ih =>
      simp only [cexecOps, Nat.cast_add, ChargedProgram.answerWith, ChargedProgram.opCost]
      exact add_le_add le_rfl (ih _ _)

/-- The credit argument also bounds an actual capped trace when membership is
answered by computation. Each remaining query reserves both the arithmetic it
unlocks in CV18 and the arithmetic needed to compute its answer. -/
theorem cexecOps_le_of_credit {M a s : ℕ} {P : ChargedProgram d α} {Q : α → ℕ → Prop}
    (hM : ∀ x, (member x).cost ≤ M) (hP : ChargedProgram.OpCredit a P s Q)
    (b : ℕ) (t : Tape d) : cexecOps member P b t ≤ s + (a + M) * b := by
  induction P generalizing s b t with
  | pure r => exact Nat.zero_le _
  | query x k ih =>
      cases b with
      | zero => exact Nat.zero_le _
      | succ b =>
          have hz : ((b + 1 : ℕ) : ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero b
          simp only [cexecOps, hz, ite_false, enat_succ_sub_one, Nat.mul_succ]
          have hk := ih (member x).value (hP (member x).value) b t
          have hx := hM x
          omega
  | randomNat law k ih => exact ih 0 (hP 0) b t
  | randomPoint law h k ih => exact ih _ (hP (t 0).2.1) b t.tail
  | randomReal law h k ih => exact ih _ (hP (t 0).2.2) b t.tail
  | tick c k ih =>
      have hc := hP.1
      have hk := ih hP.2 b t
      change ttc.ChargedCV18.opsTotal c + cexecOps member k b t ≤ _
      omega

end ttc.Tape
