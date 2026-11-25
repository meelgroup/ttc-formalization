/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Law
import ArlibCommunity.Algorithms.CV18.Analysis.ModelSupport

/-!
# Measurability of a tree's run

`Tree.tapeLaw_map_exec` needs the outcome of a run to be a measurable function of the
tape.  `MeasFam f` says that a family `f a` of trees runs measurably in its argument, the
calls left and the tape together.  It is closed under the ways the program is built:
results computed by measurable maps, sequencing, steps of charged arithmetic with
measurable values, reads of the tape, changes to the query cap, and case splits.

A sealed number carries the measurable structure of the number it holds (`Num.get`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ArlibCommunity.Algorithms.CV18 (measurable_some)

/-! ## Sealed numbers are measurable through their values -/

instance Num.instMeasurableSpace {α : Type} [MeasurableSpace α] : MeasurableSpace (Num α) :=
  MeasurableSpace.comap Num.get inferInstance

theorem Num.measurable_get {α : Type} [MeasurableSpace α] : Measurable (Num.get : Num α → α) :=
  comap_measurable _

/-- A map into sealed numbers is measurable when the numbers it holds are. -/
theorem Num.measurable_of_get {X α : Type} [MeasurableSpace X] [MeasurableSpace α]
    {f : X → Num α} (hf : Measurable fun x => (f x).get) : Measurable f := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact hf ht

theorem Num.measurable_iff {X α : Type} [MeasurableSpace X] [MeasurableSpace α]
    {f : X → Num α} : Measurable f ↔ Measurable fun x => (f x).get :=
  ⟨fun h => Num.measurable_get.comp h, Num.measurable_of_get⟩

/-! ## Measurable families of trees -/

namespace Tree

variable {n : ℕ} {A A' β γ : Type}

theorem exec_bind (p : Tree n β) (f : β → Tree n γ) (b : ℕ) (t : Tape n) :
    exec (p.bind f) b t =
      match exec p b t with
      | (none, m, b', t') => (none, m, b', t')
      | (some a, m, b', t') =>
          let r := exec (f a) b' t'
          (r.1, m + r.2.1, r.2.2) := by
  induction p generalizing b t with
  | pure a =>
      show exec (f a) b t = _
      simp [exec]
  | fail => rfl
  | step c k ih =>
      simp only [bind, exec, ih]
      rcases exec (k c.val) b t with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | coin k ih =>
      simp only [bind, exec, ih]
      rcases exec (k (t 0).1) b t.tail with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | unit k ih =>
      simp only [bind, exec, ih]
      rcases exec (k (t 0).2.2) b t.tail with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | gaussian k ih =>
      simp only [bind, exec, ih]
      rcases exec (k (t 0).2.1) b t.tail with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | poisson r k ih =>
      simp only [bind, exec, ih]
      rcases exec (k _) b t.tail with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | binom N k ih =>
      simp only [bind, exec, ih]
      rcases exec (k _) b t.tail with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | setBudget c k ih =>
      simp only [bind, exec, ih]
      rcases exec k c.get t with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | spend k ih =>
      cases b with
      | zero => exact ih false 0 t
      | succ b => exact ih true b t

variable [MeasurableSpace A] [MeasurableSpace A'] [MeasurableSpace β] [MeasurableSpace γ]

/-- **A family of trees runs measurably**: the run `exec (f a) b t` is a measurable
function of the argument `a`, the calls left `b` and the tape `t` together. -/
def MeasFam (f : A → Tree n β) : Prop :=
  Measurable fun p : A × ℕ × Tape n => exec (f p.1) p.2.1 p.2.2

theorem MeasFam.comp {f : A → Tree n β} (hf : MeasFam f) {φ : A' → A} (hφ : Measurable φ) :
    MeasFam fun a => f (φ a) :=
  Measurable.comp hf ((hφ.comp measurable_fst).prodMk measurable_snd)

theorem MeasFam.congr {f g : A → Tree n β} (hf : MeasFam f) (h : ∀ a, f a = g a) :
    MeasFam g := by
  have : f = g := funext h
  exact this ▸ hf

theorem MeasFam.pure {g : A → β} (hg : Measurable g) :
    MeasFam fun a => Tree.pure (n := n) (g a) :=
  (measurable_some.comp (hg.comp measurable_fst)).prodMk
    (measurable_const.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))

theorem MeasFam.fail : MeasFam fun _ : A => (Tree.fail : Tree n β) :=
  measurable_const.prodMk (measurable_const.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))

/-- The outcome of a run is measurable when the family runs measurably. -/
theorem MeasFam.outcome {f : A → Tree n β} (hf : MeasFam f) (a : A) (b : ℕ) :
    Measurable fun t => outcome (exec (f a) b t) := by
  have h2 : Measurable fun t : Tape n => ((a, b, t) : A × ℕ × Tape n) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have h3 : Measurable fun t : Tape n => exec (f a) b t := (show Measurable _ from hf).comp h2
  exact h3.fst.prodMk (h3.snd.fst.prodMk h3.snd.snd.fst)

/-- Sequencing. -/
theorem MeasFam.bind [Inhabited β] {f : A → Tree n β} {h : A × β → Tree n γ}
    (hf : MeasFam f) (hh : MeasFam h) :
    MeasFam fun a => (f a).bind fun x => h (a, x) := by
  let Φ : (A × ℕ × ℕ × Tape n) × Option β → Option γ × ℕ × ℕ × Tape n := fun p =>
    match p.2 with
    | none => (none, p.1.2.1, p.1.2.2.1, p.1.2.2.2)
    | some x =>
        let r := exec (h (p.1.1, x)) p.1.2.2.1 p.1.2.2.2
        (r.1, p.1.2.1 + r.2.1, r.2.2)
  have hΦ : Measurable Φ := by
    refine ArlibCommunity.Algorithms.CV18.Measurable.optionCases (α := β) (γ := A × ℕ × ℕ × Tape n) (default : β)
      (noneValue := fun q => (none, q.2.1, q.2.2.1, q.2.2.2))
      (someValue := fun q =>
        let r := exec (h (q.1.1, q.2)) q.1.2.2.1 q.1.2.2.2
        (r.1, q.1.2.1 + r.2.1, r.2.2))
      (measurable_const.prodMk (measurable_snd.fst.prodMk
        (measurable_snd.snd.fst.prodMk measurable_snd.snd.snd))) ?_
    have hr : Measurable fun q : (A × ℕ × ℕ × Tape n) × β =>
        exec (h (q.1.1, q.2)) q.1.2.2.1 q.1.2.2.2 :=
      Measurable.comp hh ((measurable_fst.fst.prodMk measurable_snd).prodMk
        (measurable_fst.snd.snd.fst.prodMk measurable_fst.snd.snd.snd))
    exact hr.fst.prodMk ((measurable_fst.snd.fst.add hr.snd.fst).prodMk hr.snd.snd)
  have hrun : Measurable fun p : A × ℕ × Tape n =>
      ((p.1, (exec (f p.1) p.2.1 p.2.2).2), (exec (f p.1) p.2.1 p.2.2).1) :=
    (measurable_fst.prodMk hf.snd).prodMk hf.fst
  have heq : (fun p : A × ℕ × Tape n => exec ((f p.1).bind fun x => h (p.1, x)) p.2.1 p.2.2) =
      Φ ∘ fun p : A × ℕ × Tape n =>
        ((p.1, (exec (f p.1) p.2.1 p.2.2).2), (exec (f p.1) p.2.1 p.2.2).1) := by
    funext p
    rw [exec_bind]
    simp only [Function.comp_apply, Φ]
    rcases exec (f p.1) p.2.1 p.2.2 with ⟨_ | x, m, b', t'⟩ <;> rfl
  unfold MeasFam
  rw [heq]
  exact hΦ.comp hrun

/-- A step of charged arithmetic whose value and cost depend measurably on the
argument. -/
theorem MeasFam.step {δ : Type} [MeasurableSpace δ] {c : A → Prog δ}
    (hv : Measurable fun a => (c a).val) (hc : Measurable fun a => opsTotal (c a).cost)
    {k : A × δ → Tree n β} (hk : MeasFam k) :
    MeasFam fun a => Tree.step (c a) fun x => k (a, x) := by
  have hr : Measurable fun p : A × ℕ × Tape n => exec (k (p.1, (c p.1).val)) p.2.1 p.2.2 :=
    Measurable.comp hk ((measurable_fst.prodMk (hv.comp measurable_fst)).prodMk
      measurable_snd)
  exact hr.fst.prodMk (((hc.comp measurable_fst).add hr.snd.fst).prodMk hr.snd.snd)

/-- Reading a component `π` of the next round, and spending `j` operations. -/
private theorem MeasFam.read {X : Type} [MeasurableSpace X] (π : Round n → X)
    (hπ : Measurable π) (j : ℕ) {k : A × X → Tree n β} (hk : MeasFam k)
    {f : A → Tree n β}
    (hf : ∀ a b t, exec (f a) b t =
      let r := exec (k (a, π (t 0))) b t.tail
      (r.1, j + r.2.1, r.2.2)) :
    MeasFam f := by
  have hr : Measurable fun p : A × ℕ × Tape n =>
      exec (k (p.1, π (p.2.2 0))) p.2.1 p.2.2.tail :=
    Measurable.comp hk ((measurable_fst.prodMk (hπ.comp ((measurable_pi_apply 0).comp
      measurable_snd.snd))).prodMk (measurable_snd.fst.prodMk
        (measurable_tape_tail.comp measurable_snd.snd)))
  have heq : (fun p : A × ℕ × Tape n => exec (f p.1) p.2.1 p.2.2) =
      fun p => let r := exec (k (p.1, π (p.2.2 0))) p.2.1 p.2.2.tail
        (r.1, j + r.2.1, r.2.2) := by
    funext p
    exact hf _ _ _
  unfold MeasFam
  rw [heq]
  exact hr.fst.prodMk ((measurable_const.add hr.snd.fst).prodMk hr.snd.snd)

theorem MeasFam.coin {k : A × Bool → Tree n β} (hk : MeasFam k) :
    MeasFam fun a => Tree.coin fun x => k (a, x) :=
  MeasFam.read (fun r => r.1) measurable_fst 1 hk fun _ _ _ => rfl

theorem MeasFam.unit {k : A × ℝ → Tree n β} (hk : MeasFam k) :
    MeasFam fun a => Tree.unit fun v => k (a, v) :=
  MeasFam.read (fun r => r.2.2) (measurable_snd.comp measurable_snd) 1 hk fun _ _ _ => rfl

theorem MeasFam.gaussian {k : A × EuclideanSpace ℝ (Fin n) → Tree n β} (hk : MeasFam k) :
    MeasFam fun a => Tree.gaussian fun g => k (a, g) :=
  MeasFam.read (fun r => r.2.1) (measurable_fst.comp measurable_snd) n hk fun _ _ _ => rfl

/-- A case split on a measurable condition. -/
theorem MeasFam.ite {P : A → Prop} [DecidablePred P] (hP : MeasurableSet {a | P a})
    {f g : A → Tree n β} (hf : MeasFam f) (hg : MeasFam g) :
    MeasFam fun a => if P a then f a else g a := by
  have heq : (fun p : A × ℕ × Tape n => exec (if P p.1 then f p.1 else g p.1) p.2.1 p.2.2) =
      fun p => if p.1 ∈ {a | P a} then exec (f p.1) p.2.1 p.2.2
        else exec (g p.1) p.2.1 p.2.2 := by
    funext p
    by_cases h : P p.1 <;> simp [h]
  unfold MeasFam
  rw [heq]
  exact Measurable.ite (measurable_fst hP) (f := fun p : A × ℕ × Tape n =>
    exec (f p.1) p.2.1 p.2.2) hf hg

/-- A case split on a flag. -/
theorem MeasFam.bool {f g : A → Tree n β} (hf : MeasFam f) (hg : MeasFam g) :
    MeasFam fun p : A × Bool => if p.2 = true then f p.1 else g p.1 :=
  MeasFam.ite (measurable_snd (measurableSet_singleton true))
    (hf.comp measurable_fst) (hg.comp measurable_fst)

/-- A case split on an optional value. -/
theorem MeasFam.option [Inhabited β] {f : A → Tree n γ} {g : A × β → Tree n γ}
    (hf : MeasFam f) (hg : MeasFam g) :
    MeasFam fun p : A × Option β =>
      match p.2 with
      | none => f p.1
      | some x => g (p.1, x) := by
  let Φ : (A × ℕ × Tape n) × Option β → Option γ × ℕ × ℕ × Tape n := fun p =>
    match p.2 with
    | none => exec (f p.1.1) p.1.2.1 p.1.2.2
    | some x => exec (g (p.1.1, x)) p.1.2.1 p.1.2.2
  have hΦ : Measurable Φ :=
    ArlibCommunity.Algorithms.CV18.Measurable.optionCases (α := β) (γ := A × ℕ × Tape n) (default : β)
      (noneValue := fun q => exec (f q.1) q.2.1 q.2.2)
      (someValue := fun q => exec (g (q.1.1, q.2)) q.1.2.1 q.1.2.2) hf
      (Measurable.comp hg ((measurable_fst.fst.prodMk measurable_snd).prodMk
        (measurable_fst.snd.fst.prodMk measurable_fst.snd.snd)))
  have heq : (fun p : (A × Option β) × ℕ × Tape n =>
      exec (match p.1.2 with
        | none => f p.1.1
        | some x => g (p.1.1, x)) p.2.1 p.2.2) =
      Φ ∘ fun p : (A × Option β) × ℕ × Tape n => ((p.1.1, p.2), p.1.2) := by
    funext p
    rcases p with ⟨⟨a, _ | x⟩, b, t⟩ <;> rfl
  unfold MeasFam
  rw [heq]
  exact hΦ.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

end Tree

end ttc.Tape
