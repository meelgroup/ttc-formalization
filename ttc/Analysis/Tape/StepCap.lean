/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.StepFold

/-! # The pointwise population cap after a successful sealed step -/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {d : ℕ} {α β : Type}

/-- A loop that adds at most one per round grows an accumulator by at most
its iteration count. If its fuel runs out earlier, there is no result. -/
theorem post_loopRounds_size {body : α → Tree d (α ⊕ β)} (size : α → ℕ)
    (hbody : ∀ a, Post (body a) fun r => r.elim (fun a' => size a' ≤ size a + 1) (fun _ => False)) :
    ∀ (n : ℕ) (a : α), Post (loopRounds body n a) fun r =>
      r.elim (fun a' => size a' ≤ size a + n) (fun _ => False)
  | 0, a => Nat.le_refl _
  | n + 1, a => by
      apply Post.bind ((hbody a).mono ?_)
      rintro (a' | e) hr
      · exact (post_loopRounds_size size hbody n a').mono fun z hz => by
          rcases z with a'' | e
          · change size a'' ≤ size a' + n at hz
            change size a'' ≤ size a + (n + 1)
            change size a' ≤ size a + 1 at hr
            omega
          · exact hz
      · exact hr.elim

/-- Whenever the halving loop returns, the pending and stored populations
fit the threshold together. -/
theorem post_halveT_capped (K : Params) :
    ∀ (f : ℕ) (p : Num ℝ) (X : List (Fin d → Num ℤ)) (size N : Num ℕ),
      size.get = X.length →
      Post (halveT K f p X size N) fun h =>
        h.2.2.1.get = h.2.1.length ∧ ((h.2.1.length + h.2.2.2.get : ℕ) : ℝ) ≤ K.thresh.get
  | 0, _, _, _, _, _ => trivial
  | f + 1, p, X, size, N, hsize => by
      unfold halveT
      refine post_compute_bind ?_
      have ht : (do
          let total ← A.add size N
          let totalR ← A.cast total
          A.le totalR K.thresh : Prog Bool).val =
          decide (((X.length + N.get : ℕ) : ℝ) ≤ K.thresh.get) := by
        simp only [Charged.val_bind, A.le, A.cast, A.add, Num.val_le, Num.get_cast,
          Num.get_add, hsize]
      rw [ht]
      by_cases h : ((X.length + N.get : ℕ) : ℝ) ≤ K.thresh.get
      · simp only [h, decide_true, ite_true]
        exact ⟨hsize, h⟩
      · simp only [h, decide_false, Bool.false_eq_true, ite_false]
        refine Post.bind ((post_filterCopiesT _ X).mono fun r hr => ?_)
        refine Post.bind (post_of_forall (fun N' => ?_) _)
        exact post_compute_bind (post_halveT_capped K f _ _ _ N' hr)

/-- The sampler never appends more than the pending batch, even on tapes on
which the retries run out of fuel. -/
theorem post_sampleT_size (fuel : ℕ) (K : Params) (L : Loaded d)
    (sc : Fin L.facets → Num ℝ) (h : Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ) :
    Post (sampleT fuel K L sc h) fun s => s.X.length ≤ h.2.1.length + h.2.2.2.get := by
  unfold sampleT
  refine post_compute_bind ?_
  show Post ((loopRounds _ h.2.2.2.get (h.2.1, h.2.2.1)).bind _) _
  refine Post.bind ((post_loopRounds_size (fun acc : List (Fin d → Num ℤ) × Num ℕ => acc.1.length)
    (fun acc => ?_) _ _).mono ?_)
  · unfold sampleBody
    refine Post.bind (post_of_forall (fun z => ?_) _)
    refine post_compute_bind (post_compute_bind ?_)
    change (A.push acc.1 z).val.length ≤ acc.1.length + 1
    simp [A.push, ttc.Model.Operations.push, Charged.val_op]
  · rintro (acc | e) hr
    · exact hr
    · exact e.elim

/-- Every returned component state stores at most the threshold number of
copies. This invariant bounds the input size of the next component's scans. -/
theorem post_stepT_capped (f : ℕ) (K : Params) (L : Loaded d) (s : State d) (hp : 0 ≤ s.p.get) :
    Post (stepT (cv18T d) f K L s) fun s' =>
      (s'.X.length : ℝ) ≤ K.thresh.get := by
  rw [stepT_eq]
  refine post_compute_bind (post_compute_bind (Post.bind (post_of_forall (fun v => ?_) _)))
  refine post_compute_bind (post_compute_bind ?_)
  refine Post.bind ((post_rateT _ _ _ _ s hp).mono fun q hq => ?_)
  rw [tailT_eq]
  refine post_compute_bind (Post.bind (post_of_forall (fun N => ?_) _))
  refine Post.bind ((post_halveT_capped K f q.1 q.2.1 q.2.2 N hq.2).mono fun h hh => ?_)
  refine (post_sampleT_size f K L _ h).mono fun s' hs => ?_
  have hs' : (s'.X.length : ℝ) ≤ ((h.2.1.length + h.2.2.2.get : ℕ) : ℝ) := by exact_mod_cast hs
  exact hs'.trans hh.2

end ttc.Tape
