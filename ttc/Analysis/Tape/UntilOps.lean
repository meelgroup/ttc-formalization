/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.OpsExp

/-! # Expected cost of a first-exit loop from its survival probabilities -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open ttc.Model.Operations
open ttc.SealedRun (tapeLaw)
open ttc.Tape.Tree

variable {d : ℕ} {α β : Type}

/-- With zero fuel no round is executed. A round either supplies the next
state or returns the final result. -/
def untilFuel (round : α → Tree d (α ⊕ β)) : ℕ → α → Tree d β
  | 0, _ => .fail
  | n + 1, a => (round a).bind fun r => r.elim (untilFuel round n) Tree.pure

/-- Increasing the fuel by one can add at most one round of work, and only on
the tapes where the previous fuel did not finish. -/
theorem exec_untilFuel_succ_ops_le (round : α → Tree d (α ⊕ β)) (I : α → Prop) (B : ℕ)
    (hI : ∀ a, I a → Post (round a) fun r => r.elim I (fun _ => True))
    (hB : ∀ a, I a → ∀ b t, (exec (round a) b t).2.1 ≤ B) :
    ∀ (f : ℕ) (a : α), I a → ∀ (b : ℕ) (t : Tape d),
      (exec (untilFuel round (f + 1) a) b t).2.1 ≤ (exec (untilFuel round f a) b t).2.1 +
        (if (exec (untilFuel round f a) b t).1.isNone then B else 0)
  | 0, a, ha, b, t => by
      have hr := hB a ha b t
      rw [untilFuel, untilFuel, exec_bind]
      rcases h : exec (round a) b t with ⟨o, j, b', t'⟩
      rw [h] at hr
      rcases o with _ | (_ | _) <;>
        simpa [untilFuel, exec] using hr
  | f + 1, a, ha, b, t => by
      rw [untilFuel, untilFuel, exec_bind, exec_bind]
      have post := hI a ha
      rcases h : exec (round a) b t with ⟨o, j, b', t'⟩
      rcases o with _ | (a' | c)
      · simp
      · have ha' : I a' := exec_post post b t (a := Sum.inl a') (by rw [h])
        have hi := exec_untilFuel_succ_ops_le round I B hI hB f a' ha' b' t'
        exact (Nat.add_le_add_left hi j).trans_eq (Nat.add_assoc _ _ _).symm
      · simp [exec]

/-- A first-exit loop pays the round bound times the sum of probabilities of
still running, up to the prescribed fuel. -/
theorem Eops_untilFuel_le [MeasurableSpace β] (round : α → Tree d (α ⊕ β)) (I : α → Prop) (B : ℕ)
    (hI : ∀ a, I a → Post (round a) fun r => r.elim I (fun _ => True))
    (hB : ∀ a, I a → ∀ b t, (exec (round a) b t).2.1 ≤ B)
    (b : ℕ) (a : α) (ha : I a)
    (hm : ∀ f, Measurable fun t => outcome (exec (untilFuel round f a) b t)) :
    ∀ f, Eops (untilFuel round f a) b ≤
      (B : ENNReal) * ∑ j ∈ Finset.range f, vlaw (untilFuel round j a) b {none} := by
  intro f
  induction f with
  | zero => simp [untilFuel]
  | succ f ih =>
      have hs (t : Tape d) :
          t ∈ (fun t => (exec (untilFuel round f a) b t).1) ⁻¹' ({none} : Set (Option β)) ↔
            (exec (untilFuel round f a) b t).1.isNone := by
        change (exec (untilFuel round f a) b t).1 = none ↔ _
        cases (exec (untilFuel round f a) b t).1 <;> simp
      let failSet : Set (Tape d) := (fun t => (exec (untilFuel round f a) b t).1) ⁻¹' {none}
      have hmeas : MeasurableSet failSet := (measurable_fst.comp (hm f)) measurableSet_none
      have hmops : Measurable fun t => ((exec (untilFuel round f a) b t).2.1 : ENNReal) :=
        measurable_ops.comp (hm f)
      have hmass : tapeLaw d failSet = vlaw (untilFuel round f a) b {none} := by
        rw [vlaw, ← tapeLaw_map_exec _ _ (hm f), Measure.map_map measurable_fst (hm f),
          Measure.map_apply (measurable_fst.comp (hm f)) measurableSet_none]
        rfl
      have htail : Eops (untilFuel round (f + 1) a) b ≤
          Eops (untilFuel round f a) b + (B : ENNReal) * vlaw (untilFuel round f a) b {none} := by
        rw [Eops_eq_tape _ _ (hm (f + 1)), Eops_eq_tape _ _ (hm f), ← hmass,
          ← lintegral_indicator_const hmeas (B : ENNReal),
          ← lintegral_add_left hmops]
        refine lintegral_mono fun t => ?_
        have h := exec_untilFuel_succ_ops_le round I B hI hB f a ha b t
        by_cases ht : t ∈ failSet
        · have he : (exec (untilFuel round f a) b t).1.isNone := (hs t).mp ht
          rw [ite_eq_left he] at h
          rw [indicator_of_mem ht, ← Nat.cast_add]
          exact Nat.cast_le.mpr h
        · have he : ¬ (exec (untilFuel round f a) b t).1.isNone := fun h => ht ((hs t).mpr h)
          rw [ite_eq_right he, add_zero] at h
          rw [indicator_of_notMem ht, add_zero]
          exact Nat.cast_le.mpr h
      exact htail.trans (by rw [Finset.sum_range_succ, mul_add]; exact add_le_add ih le_rfl)

end ttc.Tape
