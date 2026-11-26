/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.StepSamples

/-!
# What every run of a tree gives

`Post p Q` says that every result `p` gives, on any tape, satisfies `Q`.  It is read off
the tree, and gives `Q` almost surely under the result law (`ae_vlaw_post`).  The halving
loop and the step keep the count equal to the list's length and `p ≥ 0`
(`post_halveT`, `post_filterCopiesT`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {d : ℕ}

section Post

variable {α β γ : Type}

/-- **Every result of `p` satisfies `Q`.** -/
def Post : Tree d α → (α → Prop) → Prop
  | .pure a, Q => Q a
  | .fail, _ => True
  | .step c k, Q => Post (k c.val) Q
  | .coin k, Q => ∀ x, Post (k x) Q
  | .unit k, Q => ∀ x, Post (k x) Q
  | .gaussian k, Q => ∀ x, Post (k x) Q
  | .poisson _ k, Q => ∀ x, Post (k x) Q
  | .binom _ k, Q => ∀ x, Post (k x) Q
  | .setBudget _ k, Q => Post k Q
  | .spend k, Q => ∀ x, Post (k x) Q

theorem Post.bind {p : Tree d α} {f : α → Tree d β} {Q : β → Prop}
    (hp : Post p fun a => Post (f a) Q) : Post (p.bind f) Q := by
  induction p with
  | pure a => exact hp
  | fail => trivial
  | step c k ih => exact ih c.val hp
  | coin k ih => exact fun x => ih x (hp x)
  | unit k ih => exact fun x => ih x (hp x)
  | gaussian k ih => exact fun x => ih x (hp x)
  | poisson r k ih => exact fun x => ih x (hp x)
  | binom N k ih => exact fun x => ih x (hp x)
  | setBudget c k ih => exact ih hp
  | spend k ih => exact fun x => ih x (hp x)

theorem Post.mono {p : Tree d α} {Q R : α → Prop} (hp : Post p Q) (h : ∀ a, Q a → R a) :
    Post p R := by
  induction p with
  | pure a => exact h a hp
  | fail => trivial
  | step c k ih => exact ih c.val hp
  | coin k ih => exact fun x => ih x (hp x)
  | unit k ih => exact fun x => ih x (hp x)
  | gaussian k ih => exact fun x => ih x (hp x)
  | poisson r k ih => exact fun x => ih x (hp x)
  | binom N k ih => exact fun x => ih x (hp x)
  | setBudget c k ih => exact ih hp
  | spend k ih => exact fun x => ih x (hp x)

theorem post_of_forall {Q : α → Prop} (h : ∀ a, Q a) : ∀ p : Tree d α, Post p Q := by
  intro p
  induction p with
  | pure a => exact h a
  | fail => trivial
  | step c k ih => exact ih c.val
  | coin k ih => exact ih
  | unit k ih => exact ih
  | gaussian k ih => exact ih
  | poisson r k ih => exact ih
  | binom N k ih => exact ih
  | setBudget c k ih => exact ih
  | spend k ih => exact ih

theorem post_compute {c : Prog α} {Q : α → Prop} (h : Q c.val) : Post (compute (n := d) c) Q := h

theorem post_pure {a : α} {Q : α → Prop} (h : Q a) : Post (Tree.pure (n := d) a) Q := h

theorem post_compute_bind {c : Prog α} {f : α → Tree d β} {Q : β → Prop} (h : Post (f c.val) Q) :
    Post ((compute c).bind f) Q := h

theorem post_ite (c : Bool) {p q : Tree d α} {Q : α → Prop} (hp : Post p Q) (hq : Post q Q) :
    Post (if c then p else q) Q := by cases c <;> assumption

theorem post_foldlM {ι : Type} {g : β → ι → Tree d β} {I : β → Prop}
    (hg : ∀ b x, I b → Post (g b x) I) : ∀ (l : List ι) (b : β), I b → Post (l.foldlM g b) I
  | [], b, hb => hb
  | x :: l, b, hb => by
      simp only [List.foldlM_cons]
      exact Post.bind ((hg b x hb).mono fun b' hb' => post_foldlM hg l b' hb')

theorem post_loopRounds {body : β → Tree d (β ⊕ γ)} {I : β → Prop} {R : γ → Prop}
    (hb : ∀ y, I y → Post (body y) fun r => r.elim I R) :
    ∀ (k : ℕ) (y : β), I y → Post (loopRounds body k y) fun r => r.elim I R
  | 0, y, hy => hy
  | k + 1, y, hy => by
      show Post ((body y).bind _) _
      refine Post.bind ((hb y hy).mono fun r hr => ?_)
      rcases r with y' | c
      · exact post_loopRounds hb k y' hr
      · exact hr

/-- **A result of a run satisfies `Q`.** -/
theorem exec_post {p : Tree d α} {Q : α → Prop} (hp : Post p Q) (b : ℕ) (t : Tape d) {a : α}
    (h : (exec p b t).1 = some a) : Q a := by
  induction p generalizing b t with
  | pure a' =>
      cases h
      exact hp
  | fail => cases h
  | step c k ih => exact ih c.val hp b t h
  | coin k ih => exact ih _ (hp _) b _ h
  | unit k ih => exact ih _ (hp _) b _ h
  | gaussian k ih => exact ih _ (hp _) b _ h
  | poisson r k ih => exact ih _ (hp _) b _ h
  | binom N k ih => exact ih _ (hp _) b _ h
  | setBudget c k ih => exact ih hp _ _ h
  | spend k ih =>
      cases b with
      | zero => exact ih _ (hp _) 0 t h
      | succ b => exact ih _ (hp _) b t h

theorem measurableSet_forall_mem [MeasurableSpace α] {Q : α → Prop} (hQ : MeasurableSet {a | Q a}) :
    MeasurableSet {o : Option α | ∀ a ∈ o, Q a} := by
  have : {o : Option α | ∀ a ∈ o, Q a} = {none} ∪ some '' {a | Q a} := by
    ext o
    rcases o with _ | a <;> simp
  rw [this]
  exact measurableSet_none.union (measurableSet_image_some hQ)

/-- **What every run gives holds almost surely.** -/
theorem ae_vlaw_post [MeasurableSpace α] {p : Tree d α} {Q : α → Prop} (hp : Post p Q)
    (hQ : MeasurableSet {a | Q a}) (b : ℕ) (hm : Measurable fun t => outcome (exec p b t)) :
    ∀ᵐ o ∂vlaw p b, ∀ a ∈ o, Q a := by
  rw [vlaw, ← tapeLaw_map_exec p b hm, Measure.map_map measurable_fst hm,
    ae_map_iff (measurable_fst.comp hm).aemeasurable (measurableSet_forall_mem hQ)]
  exact ae_of_all _ fun t a ha => exec_post hp b t ha

end Post

/-! ## The loops keep the count -/

section Count

theorem post_filterCopiesT (keep : (Fin d → Num ℤ) → Tree d Bool) (X : List (Fin d → Num ℤ)) :
    Post (filterCopiesT keep X) fun r => r.2.get = r.1.length := by
  unfold filterCopiesT
  refine post_compute_bind (post_compute_bind ?_)
  refine post_foldlM (I := fun acc : List (Fin d → Num ℤ) × Num ℕ => acc.2.get = acc.1.length)
    (fun acc x hacc => ?_) X _ (by simp [A.lit])
  refine post_compute_bind (Post.bind (post_of_forall (fun k => ?_) _))
  cases k
  · exact hacc
  · simp only [ite_true]
    refine post_compute_bind (post_compute_bind ?_)
    show (A.add acc.2 _).val.get = (A.push acc.1 _).val.length
    simp [A.push, ttc.Model.Operations.push, A.add, A.lit, Num.get_add, hacc]

theorem post_halveT (K : Params) :
    ∀ (f : ℕ) (p : Num ℝ) (X : List (Fin d → Num ℤ)) (size N : Num ℕ),
      size.get = X.length → 0 ≤ p.get →
      Post (halveT K f p X size N) fun h => h.2.2.1.get = h.2.1.length ∧ 0 ≤ h.1.get
  | 0, _, _, _, _, _, _ => trivial
  | f + 1, p, X, size, N, hs, hp => by
      unfold halveT
      refine post_compute_bind (post_ite _ ⟨hs, hp⟩ ?_)
      refine Post.bind ((post_filterCopiesT _ X).mono fun r hr => ?_)
      refine Post.bind (post_of_forall (fun N' => ?_) _)
      refine post_compute_bind (post_halveT K f _ _ _ _ hr ?_)
      simp only [A.divLit, A.div, A.lit, Charged.val_bind, Num.get_div, Num.get_lit]
      positivity

end Count

end ttc.Tape
