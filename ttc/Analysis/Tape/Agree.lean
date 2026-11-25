/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Interp

/-!
# Computations that agree, and loops as trees

Two computations of the program monad **agree** (`Agree`) when, from every oracle, they
give the same result, the same oracle left, and the same operations.  This is what the
bridge needs of the program and its tree: it says nothing about arlib's space profile,
which no claim here reads.  Agreement is preserved by sequencing (`Agree.bind`).

`loopUntil` (arlib's `Num.iterateWhile`) agrees with the tree `loopTree`: one loop
operation, then the rounds (`loopRounds`).
-/

set_option autoImplicit false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged CostVec NumOp)
open ttc.Model.Operations
open ttc.Program

variable {n : ℕ} {α β γ : Type}

/-- **Two computations agree**: from every oracle, the same result and oracle left, and
the same tally. -/
def Agree (X Y : M n α) : Prop :=
  ∀ o, (runFrom X o).val = (runFrom Y o).val ∧ (runFrom X o).cost = (runFrom Y o).cost

theorem Agree.refl (X : M n α) : Agree X X := fun _ => ⟨rfl, rfl⟩

theorem Agree.symm {X Y : M n α} (h : Agree X Y) : Agree Y X :=
  fun o => ⟨(h o).1.symm, (h o).2.symm⟩

theorem Agree.trans {X Y Z : M n α} (h : Agree X Y) (h' : Agree Y Z) : Agree X Z :=
  fun o => ⟨(h o).1.trans (h' o).1, (h o).2.trans (h' o).2⟩

theorem Agree.of_eq {X Y : M n α} (h : X = Y) : Agree X Y := h ▸ Agree.refl X

theorem Agree.bind {X Y : M n α} {F G : α → M n β} (hXY : Agree X Y)
    (hFG : ∀ a, Agree (F a) (G a)) : Agree (X >>= F) (Y >>= G) := by
  intro o
  refine ⟨?_, ?_⟩
  · rw [val_runFrom_bind, val_runFrom_bind, (hXY o).1]
    rcases (runFrom Y o).val with ⟨_ | a, o'⟩
    · rfl
    · exact (hFG a o').1
  · rw [cost_runFrom_bind, cost_runFrom_bind, (hXY o).1, (hXY o).2]
    rcases (runFrom Y o).val with ⟨_ | a, o'⟩
    · rfl
    · simp only [(hFG a o').2]

theorem Agree.bind_right (X : M n α) {F G : α → M n β} (hFG : ∀ a, Agree (F a) (G a)) :
    Agree (X >>= F) (X >>= G) :=
  Agree.bind (Agree.refl X) hFG

/-- Agreement gives the same `interp_run` reading. -/
theorem Agree.run {X : M n α} {p : Tree n α} (h : Agree X (Tree.interp p)) (b : ℕ)
    (t : Tape n) :
    (runFrom X (Oracle.withBudget t b)).val =
        ((Tree.exec p b t).1, Oracle.withBudget (Tree.exec p b t).2.2.2 (Tree.exec p b t).2.2.1) ∧
      opsTotal (runFrom X (Oracle.withBudget t b)).cost = (Tree.exec p b t).2.1 := by
  rw [(h _).1, (h _).2]
  exact interp_run p b t

/-! ## arlib's loop with a break -/

section FoldlWhile

variable {δ ι : Type} (f : δ → ι → Prog (Option δ))

theorem val_foldlWhile_cons (a : ι) (l : List ι) (b : δ) :
    (Charged.foldlWhile f (a :: l) b).val =
      match (f b a).val with
      | none => b
      | some b' => (Charged.foldlWhile f l b').val := by
  rcases h : (f b a).val with _ | b'
  · simp only [Charged.foldlWhile]
    simp only [Charged.val] at h ⊢
    rw [h]
  · simp only [Charged.foldlWhile]
    simp only [Charged.val] at h ⊢
    rw [h]

theorem cost_foldlWhile_cons (a : ι) (l : List ι) (b : δ) :
    (Charged.foldlWhile f (a :: l) b).cost =
      (f b a).cost +
        match (f b a).val with
        | none => 0
        | some b' => (Charged.foldlWhile f l b').cost := by
  rcases h : (f b a).val with _ | b'
  · simp only [Charged.foldlWhile]
    simp only [Charged.val, Charged.cost] at h ⊢
    rw [h]
    simp
  · simp only [Charged.foldlWhile]
    simp only [Charged.val, Charged.cost] at h ⊢
    rw [h]

end FoldlWhile

/-! ## Loops as trees -/

/-- The rounds of a loop: run `body` from `b` until it stops (`inr`), at most `k` times;
`inl` is the state when the rounds run out. -/
def loopRounds (body : β → Tree n (β ⊕ γ)) : ℕ → β → Tree n (β ⊕ γ)
  | 0, b => .pure (.inl b)
  | k + 1, b => (body b).bind fun
      | .inl b' => loopRounds body k b'
      | .inr c => .pure (.inr c)

/-- **A loop of `count` rounds as a tree**: one `NumOp.loop`, then the rounds. -/
def loopTree (count : Num ℕ) (body : β → Tree n (β ⊕ γ)) (init : β) : Tree n (β ⊕ γ) :=
  .step (Charged.op (Op.num .loop) () : Prog Unit) fun _ => loopRounds body count.get init

/-- Interpreting a composite tree is composing the interpretations. -/
theorem interp_bind (p : Tree n α) (f : α → Tree n β) :
    Tree.interp (p.bind f) = Tree.interp p >>= fun a => Tree.interp (f a) := by
  induction p with
  | pure a => simp only [Tree.bind, Tree.interp, pure_bind]
  | fail =>
      show (failure : M n β) = (failure : M n α) >>= _
      exact (OptionT.ext (by simp)).symm
  | step c k ih => simp only [Tree.bind, Tree.interp, ih, bind_assoc]
  | coin k ih => simp only [Tree.bind, Tree.interp, ih, bind_assoc]
  | unit k ih => simp only [Tree.bind, Tree.interp, ih, bind_assoc]
  | gaussian k ih => simp only [Tree.bind, Tree.interp, ih, bind_assoc]
  | poisson r k ih => simp only [Tree.bind, Tree.interp, ih, bind_assoc]
  | binom N k ih => simp only [Tree.bind, Tree.interp, ih, bind_assoc]
  | setBudget c k ih => simp only [Tree.bind, Tree.interp, ih, bind_assoc]
  | spend k ih => simp only [Tree.bind, Tree.interp, ih, bind_assoc]

/-- The round of `loopUntil`'s `Num.iterateWhile`, on the state the loop carries. -/
def loopStep (bodyM : β → M n (β ⊕ γ)) :
    Option (β ⊕ γ) × Oracle n → ℕ → Prog (Option (Option (β ⊕ γ) × Oracle n))
  | (some (.inl b), o), _ => do
      let r ← runFrom (bodyM b) o
      pure (some r)
  | _, _ => pure none

theorem foldlWhile_dead (bodyM : β → M n (β ⊕ γ)) (s : Option (β ⊕ γ) × Oracle n)
    (hs : ∀ b o, s ≠ (some (.inl b), o)) (l : List ℕ) :
    (Charged.foldlWhile (loopStep bodyM) l s).val = s ∧
      (Charged.foldlWhile (loopStep bodyM) l s).cost = 0 := by
  cases l with
  | nil => exact ⟨rfl, rfl⟩
  | cons a l =>
      have hstep : loopStep bodyM s a = pure none := by
        rcases s with ⟨_ | (b | c), o⟩
        · rfl
        · exact absurd rfl (hs b o)
        · rfl
      refine ⟨?_, ?_⟩
      · rw [val_foldlWhile_cons, hstep]; rfl
      · rw [cost_foldlWhile_cons, hstep]; simp

theorem foldlWhile_loopRounds (bodyM : β → M n (β ⊕ γ)) (body : β → Tree n (β ⊕ γ))
    (h : ∀ b, Agree (bodyM b) (Tree.interp (body b))) :
    ∀ (l : List ℕ) (b : β) (o : Oracle n),
      (Charged.foldlWhile (loopStep bodyM) l (some (.inl b), o)).val =
          (runFrom (Tree.interp (loopRounds body l.length b)) o).val ∧
        (Charged.foldlWhile (loopStep bodyM) l (some (.inl b), o)).cost =
          (runFrom (Tree.interp (loopRounds body l.length b)) o).cost
  | [], b, o => ⟨rfl, rfl⟩
  | a :: l, b, o => by
      have hs : loopStep bodyM (some (.inl b), o) a =
          (do let r ← runFrom (bodyM b) o; pure (some r)) := rfl
      have hR : Tree.interp (loopRounds body (l.length + 1) b) =
          Tree.interp (body b) >>= fun r => Tree.interp (match r with
            | .inl b' => loopRounds body l.length b'
            | .inr c => .pure (.inr c)) := by
        rw [loopRounds, interp_bind]
      rw [List.length_cons, hR]
      obtain ⟨hv, hc⟩ := h b o
      rcases hr : (runFrom (bodyM b) o).val with ⟨_ | (b' | c), o'⟩
      · -- the round stopped the run
        have hdead := foldlWhile_dead bodyM (none, o') (by simp) l
        refine ⟨?_, ?_⟩
        · rw [val_foldlWhile_cons, hs]
          simp only [Charged.val_bind, Charged.val_pure, hr]
          rw [hdead.1, val_runFrom_bind, ← hv, hr]
        · rw [cost_foldlWhile_cons, hs]
          simp only [Charged.val_bind, Charged.val_pure, Charged.cost_bind, Charged.cost_pure,
            hr, add_zero]
          rw [hdead.2, add_zero, cost_runFrom_bind, ← hv, hr, ← hc, add_zero]
      · -- the round continues the loop
        obtain ⟨iv, ic⟩ := foldlWhile_loopRounds bodyM body h l b' o'
        refine ⟨?_, ?_⟩
        · rw [val_foldlWhile_cons, hs]
          simp only [Charged.val_bind, Charged.val_pure, hr]
          rw [iv, val_runFrom_bind, ← hv, hr]
        · rw [cost_foldlWhile_cons, hs]
          simp only [Charged.val_bind, Charged.val_pure, Charged.cost_bind, Charged.cost_pure,
            hr, add_zero]
          rw [ic, cost_runFrom_bind, ← hv, hr, ← hc]
      · -- the round ended the loop
        have hdead := foldlWhile_dead bodyM (some (.inr c), o') (by simp) l
        refine ⟨?_, ?_⟩
        · rw [val_foldlWhile_cons, hs]
          simp only [Charged.val_bind, Charged.val_pure, hr]
          rw [hdead.1, val_runFrom_bind, ← hv, hr]
          rfl
        · rw [cost_foldlWhile_cons, hs]
          simp only [Charged.val_bind, Charged.val_pure, Charged.cost_bind, Charged.cost_pure,
            hr, add_zero]
          rw [hdead.2, add_zero, cost_runFrom_bind, ← hv, hr, ← hc]
          rfl

/-- **`loopUntil` agrees with its tree** when each round does. -/
theorem loopUntil_agree (count : Num ℕ) (bodyM : β → M n (β ⊕ γ)) (body : β → Tree n (β ⊕ γ))
    (h : ∀ b, Agree (bodyM b) (Tree.interp (body b))) (init : β) :
    Agree (loopUntil count bodyM init) (Tree.interp (loopTree count body init)) := by
  intro o
  have hL : runFrom (loopUntil count bodyM init) o =
      Charged.bind (Charged.op (Op.num .loop) (some (.inl init), o))
        (Charged.repeatWhile (fun r s => loopStep bodyM s r) count.get) := by
    show Num.iterateWhile _ count _ = _
    unfold Num.iterateWhile
    congr 2
    funext r s
    rcases s with ⟨_ | (b | c), o⟩ <;> rfl
  have hR : Tree.interp (loopTree count body init) =
      run (Charged.op (Op.num .loop) () : Prog Unit) >>= fun _ =>
        Tree.interp (loopRounds body count.get init) := rfl
  obtain ⟨iv, ic⟩ := foldlWhile_loopRounds bodyM body h (List.range count.get) init o
  rw [List.length_range] at iv ic
  obtain ⟨rv, rc⟩ := run_step (o := o) (o' := o) (a := ())
    (F := fun _ => Tree.interp (loopRounds body count.get init))
    (runFrom_run (Charged.op (Op.num .loop) () : Prog Unit) o).1
  refine ⟨?_, ?_⟩
  · rw [hL, hR, val_charged_bind, Charged.val_op]
    exact iv.trans (by rw [rv])
  · rw [hL, hR, cost_charged_bind, cost_runFrom_bind, (runFrom_run _ o).1, (runFrom_run _ o).2]
    simp only [Charged.cost_op, Charged.val_op]
    rw [show Charged.repeatWhile (fun r s => loopStep bodyM s r) count.get (some (.inl init), o) =
      Charged.foldlWhile (fun b r => loopStep bodyM b r) (List.range count.get)
        (some (.inl init), o) from rfl, ic]

end ttc.Tape
