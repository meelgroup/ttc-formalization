/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Meas
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Measurability of charged computations

The program's arithmetic is charged computations of sealed numbers.  `MP f` says a family
`f a` of charged computations has a value and an operation count that depend measurably
on `a`.  It is closed under sequencing and case splits, and holds for each of arlib's
operations on sealed numbers; this file proves it for the arithmetic the program is
written with.

Lists carry the measurable structure of their length and entries (`List.encode`).  A
function of a list is measurable when it is on lists of each length, read as functions of
their entries (`measurable_of_ofFn`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ArlibCommunity.Algorithms.CV18 (measurable_some)

/-! ## Defaults -/

/-- A sealed number holding `default`. -/
instance Num.instInhabited {α : Type} [Inhabited α] : Inhabited (Num α) :=
  ⟨(Num.lit default : Prog (Num α)).val⟩

/-! ## Countably many cases -/

/-- A function given on each of countably many measurable pieces by a measurable function
is measurable. -/
theorem measurable_of_nat_cases {X γ : Type} [MeasurableSpace X] [MeasurableSpace γ]
    {K : X → ℕ} (hK : Measurable K) {G : ℕ → X → γ} (hG : ∀ k, Measurable (G k))
    {f : X → γ} (hf : ∀ x, f x = G (K x) x) : Measurable f := by
  have hjoint : Measurable fun p : X × ℕ => G p.2 p.1 :=
    measurable_from_prod_countable_left fun k => hG k
  have : f = (fun p : X × ℕ => G p.2 p.1) ∘ fun x => (x, K x) := funext hf
  rw [this]
  exact hjoint.comp (measurable_id.prodMk hK)

/-! ## Lists -/

/-- A list as its length and its entries. -/
def List.encode {α : Type} (l : List α) : ℕ × (ℕ → Option α) := (l.length, fun i => l[i]?)

instance List.instMeasurableSpace {α : Type} [MeasurableSpace α] : MeasurableSpace (List α) :=
  MeasurableSpace.comap List.encode inferInstance

section Lists

variable {X α β : Type} [MeasurableSpace X] [MeasurableSpace α] [MeasurableSpace β]

theorem List.measurable_encode : Measurable (List.encode : List α → ℕ × (ℕ → Option α)) :=
  comap_measurable _

theorem List.measurable_length : Measurable (List.length : List α → ℕ) :=
  measurable_fst.comp List.measurable_encode

theorem List.measurable_getElem? (i : ℕ) : Measurable fun l : List α => l[i]? :=
  (measurable_pi_apply i).comp (measurable_snd.comp List.measurable_encode)

/-- A map into lists is measurable when its length and entries are. -/
theorem List.measurable_of {f : X → List α} (hlen : Measurable fun x => (f x).length)
    (hget : ∀ i : ℕ, Measurable fun x => (f x)[i]?) : Measurable f := by
  have henc : Measurable fun x => List.encode (f x) :=
    hlen.prodMk (measurable_pi_iff.mpr hget)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact henc ht

theorem List.measurable_nil : Measurable fun _ : X => ([] : List α) := measurable_const

theorem List.measurable_append_singleton {f : X → List α} {g : X → α} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun x => f x ++ [g x] := by
  have hlen : Measurable fun x => (f x).length := List.measurable_length.comp hf
  refine List.measurable_of ?_ fun i => ?_
  · simpa using hlen.add_const 1
  · have heq : (fun x => (f x ++ [g x])[i]?) = fun x =>
        if (f x).length ∈ {k | i < k} then (f x)[i]?
        else if (f x).length ∈ ({i} : Set ℕ) then some (g x) else none := by
      funext x
      simp only [Set.mem_ofPred_eq, mem_singleton_iff]
      rw [List.getElem?_append]
      split_ifs with h1 h2
      · rfl
      · subst h2; simp
      · rw [List.getElem?_singleton]
        have : i - (f x).length ≠ 0 := by omega
        simp [this]
    rw [heq]
    exact Measurable.ite (hlen (Set.Countable.measurableSet (Set.to_countable _)))
      ((List.measurable_getElem? i).comp hf)
      (Measurable.ite (hlen (measurableSet_singleton i)) (measurable_some.comp hg)
        measurable_const)

theorem List.measurable_cons {f : X → α} {g : X → List α} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun x => f x :: g x := by
  have hlen : Measurable fun x => (g x).length := List.measurable_length.comp hg
  refine List.measurable_of ?_ fun i => ?_
  · simpa using hlen.add_const 1
  · cases i with
    | zero => exact (measurable_some.comp hf : _)
    | succ i => exact ((List.measurable_getElem? i).comp hg : _)

theorem List.measurable_map {h : α → β} (hh : Measurable h) :
    Measurable fun l : List α => l.map h := by
  refine List.measurable_of ?_ fun i => ?_
  · simpa using List.measurable_length (α := α)
  · have : (fun l : List α => (l.map h)[i]?) = (fun o => o.map h) ∘ fun l => l[i]? := by
      funext l; simp
    rw [this]
    refine Measurable.comp ?_ (List.measurable_getElem? i)
    convert ArlibCommunity.Algorithms.CV18.Measurable.optionElim (none : Option β)
      (someValue := fun x => some (h x)) (measurable_some.comp hh) using 1
    funext o; cases o <;> rfl

/-- The entries of a list of length `k`, as a vector. -/
def List.vec [Inhabited α] (k : ℕ) (l : List α) : Fin k → α := fun i => l[(i : ℕ)]?.getD default

theorem List.measurable_vec [Inhabited α] (k : ℕ) :
    Measurable (List.vec (α := α) k) :=
  measurable_pi_iff.mpr fun i =>
    (ArlibCommunity.Algorithms.CV18.measurable_optionGetD default).comp
      (List.measurable_getElem? i)

omit [MeasurableSpace α] in
theorem List.ofFn_vec [Inhabited α] (l : List α) : List.ofFn (List.vec l.length l) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.vec, List.getElem?_eq_getElem h2]

/-- **A function of a list is measurable when it is on the lists of each length**, read as
functions of their entries. -/
theorem measurable_of_ofFn [Inhabited α] {γ : Type} [MeasurableSpace γ]
    {F : X × List α → γ}
    (h : ∀ k, Measurable fun p : X × (Fin k → α) => F (p.1, List.ofFn p.2)) :
    Measurable F := by
  refine measurable_of_nat_cases (K := fun p : X × List α => p.2.length)
    (List.measurable_length.comp measurable_snd)
    (G := fun k p => F (p.1, List.ofFn (List.vec k p.2)))
    (fun k => (h k).comp (measurable_fst.prodMk ((List.measurable_vec k).comp measurable_snd)))
    fun p => by simp only [List.ofFn_vec]

end Lists

/-! ## Measurable charged computations -/

section MP

variable {Q Q' β γ δ : Type} [MeasurableSpace Q] [MeasurableSpace Q'] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

/-- **Q family of charged computations is measurable**: its value and its operation count
depend measurably on the argument. -/
def MP (f : Q → Prog β) : Prop :=
  Measurable (fun a => (f a).val) ∧ Measurable (fun a => opsTotal (f a).cost)

theorem MP.const (c : Prog β) : MP (fun _ : Q => c) := ⟨measurable_const, measurable_const⟩

theorem MP.comp {f : Q → Prog β} (hf : MP f) {φ : Q' → Q} (hφ : Measurable φ) :
    MP (fun a => f (φ a)) :=
  ⟨hf.1.comp hφ, hf.2.comp hφ⟩

theorem MP.congr {f g : Q → Prog β} (hf : MP f) (h : ∀ a, f a = g a) : MP g := by
  have : f = g := funext h
  exact this ▸ hf

theorem MP.pure {g : Q → β} (hg : Measurable g) : MP (fun a => (Pure.pure (g a) : Prog β)) :=
  ⟨hg, by simp only [Charged.cost_pure, opsTotal_zero]; exact measurable_const⟩

theorem MP.charged_pure {g : Q → β} (hg : Measurable g) : MP (fun a => (Charged.pure (g a) : Prog β)) :=
  MP.pure hg

/-- Q computation whose operation count does not depend on the argument. -/
theorem MP.of_val {f : Q → Prog β} (hv : Measurable fun a => (f a).val)
    (hc : ∀ a a', opsTotal (f a).cost = opsTotal (f a').cost) : MP f :=
  ⟨hv, measurable_const' hc⟩

theorem MP.bind {f : Q → Prog β} {g : Q × β → Prog γ} (hf : MP f) (hg : MP g) :
    MP (fun a => f a >>= fun x => g (a, x)) := by
  have hpair : Measurable fun a => (a, (f a).val) := measurable_id.prodMk hf.1
  refine ⟨?_, ?_⟩
  · simp only [Charged.val_bind]
    exact hg.1.comp hpair
  · simp only [Charged.cost_bind, opsTotal_add]
    exact hf.2.add (hg.2.comp hpair)

theorem MP.ite {c : Q → Bool} (hc : Measurable c) {f g : Q → Prog β} (hf : MP f) (hg : MP g) :
    MP (fun a => if c a then f a else g a) := by
  have hs : MeasurableSet {a | c a = true} := hc (measurableSet_singleton true)
  refine ⟨?_, ?_⟩
  · have : (fun a => (if c a then f a else g a).val) =
        fun a => if a ∈ {a | c a = true} then (f a).val else (g a).val := by
      funext a; by_cases h : c a = true <;> simp [h]
    rw [this]; exact Measurable.ite hs hf.1 hg.1
  · have : (fun a => opsTotal (if c a then f a else g a).cost) =
        fun a => if a ∈ {a | c a = true} then opsTotal (f a).cost else opsTotal (g a).cost := by
      funext a; by_cases h : c a = true <;> simp [h]
    rw [this]; exact Measurable.ite hs hf.2 hg.2

/-- Sequencing, with the continuation curried (so that a `do` block unifies). -/
theorem MP.bind' {f : Q → Prog β} {g : Q → β → Prog γ} (hf : MP f)
    (hg : MP (fun p : Q × β => g p.1 p.2)) : MP (fun a => f a >>= g a) :=
  MP.bind (g := fun p : Q × β => g p.1 p.2) hf hg

/-- A function of a list is measurable when it is on the lists of each length. -/
theorem MP.ofList {α : Type} [MeasurableSpace α] [Inhabited α] {F : Q × List α → Prog β}
    (h : ∀ k, MP fun p : Q × (Fin k → α) => F (p.1, List.ofFn p.2)) : MP F :=
  ⟨measurable_of_ofFn fun k => (h k).1, measurable_of_ofFn fun k => (h k).2⟩

end MP

/-! ## Measurable maps of sealed numbers -/

section NumMaps

variable {Q : Type} [MeasurableSpace Q]

/-- Functions of finitely many natural numbers are measurable. -/
theorem measurable_of_nat {γ : Type} [MeasurableSpace γ] {x : Q → Num ℕ} (hx : Measurable x)
    (F : ℕ → γ) : Measurable fun a => F (x a).get :=
  (measurable_from_nat (f := F)).comp (Num.measurable_get.comp hx)

theorem measurable_of_nat₂ {γ : Type} [MeasurableSpace γ] {x y : Q → Num ℕ} (hx : Measurable x)
    (hy : Measurable y) (F : ℕ → ℕ → γ) : Measurable fun a => F (x a).get (y a).get := by
  have : Measurable fun p : ℕ × ℕ => F p.1 p.2 := measurable_from_prod_countable_left
    fun k => measurable_from_nat
  exact this.comp ((Num.measurable_get.comp hx).prodMk (Num.measurable_get.comp hy))

theorem measurable_of_int {γ : Type} [MeasurableSpace γ] {x : Q → Num ℤ} (hx : Measurable x)
    (F : ℤ → γ) : Measurable fun a => F (x a).get :=
  (measurable_of_countable F).comp (Num.measurable_get.comp hx)

theorem measurable_of_int₂ {γ : Type} [MeasurableSpace γ] {x y : Q → Num ℤ} (hx : Measurable x)
    (hy : Measurable y) (F : ℤ → ℤ → γ) : Measurable fun a => F (x a).get (y a).get := by
  have : Measurable fun p : ℤ × ℤ => F p.1 p.2 := measurable_of_countable _
  exact this.comp ((Num.measurable_get.comp hx).prodMk (Num.measurable_get.comp hy))

theorem measurable_decide_le {F G : Q → ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measurable fun a => decide (F a ≤ G a) := by
  refine measurable_to_countable' fun b => ?_
  cases b
  · have : (fun a => decide (F a ≤ G a)) ⁻¹' {false} = {a | F a ≤ G a}ᶜ := by
      ext a; simp
    rw [this]; exact (measurableSet_le hF hG).compl
  · have : (fun a => decide (F a ≤ G a)) ⁻¹' {true} = {a | F a ≤ G a} := by
      ext a; simp
    rw [this]; exact measurableSet_le hF hG

theorem getm {x : Q → Num ℝ} (hx : Measurable x) : Measurable fun a => (x a).get :=
  Num.measurable_get.comp hx

end NumMaps

/-! ## arlib's operations -/

section Ops

open ttc.Program

variable {Q : Type} [MeasurableSpace Q]

theorem mp_lit {α : Type} [MeasurableSpace α] (c : α) : MP (fun _ : Q => A.lit c) := MP.const _

theorem mp_add {x y : Q → Num ℝ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.add (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.add, Num.get_add]; exact (getm hx).add (getm hy)))
    fun _ _ => by simp [A.add]

theorem mp_sub {x y : Q → Num ℝ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.sub (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.sub, Num.get_sub]; exact (getm hx).sub (getm hy)))
    fun _ _ => by simp [A.sub]

theorem mp_mul {x y : Q → Num ℝ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.mul (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.mul, Num.get_mul]; exact (getm hx).mul (getm hy)))
    fun _ _ => by simp [A.mul]

theorem mp_div {x y : Q → Num ℝ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.div (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.div, Num.get_div]; exact (getm hx).div (getm hy)))
    fun _ _ => by simp [A.div]

theorem mp_max {x y : Q → Num ℝ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.max (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.max, Num.get_max]; exact (getm hx).max (getm hy)))
    fun _ _ => by simp [A.max]

theorem mp_min {x y : Q → Num ℝ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.min (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.min, Num.get_min]; exact (getm hx).min (getm hy)))
    fun _ _ => by simp [A.min]

theorem mp_le {x y : Q → Num ℝ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.le (x a) (y a)) :=
  MP.of_val (by simp only [A.le, Num.val_le]; exact measurable_decide_le (getm hx) (getm hy))
    fun _ _ => by simp [A.le]

theorem mp_lt {x y : Q → Num ℝ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.lt (x a) (y a)) := by
  unfold A.lt
  exact MP.bind (mp_le hy hx |>.comp measurable_id)
    (MP.pure ((measurable_of_countable (fun b : Bool => !b)).comp measurable_snd))

theorem mp_sqrt {x : Q → Num ℝ} (hx : Measurable x) : MP (fun a => A.sqrt (x a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.sqrt, Num.get_sqrt]; exact (getm hx).sqrt))
    fun _ _ => by simp [A.sqrt]

theorem mp_log {x : Q → Num ℝ} (hx : Measurable x) : MP (fun a => A.log (x a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.log, Num.get_log]; exact (getm hx).log))
    fun _ _ => by simp [A.log]

theorem mp_exp {x : Q → Num ℝ} (hx : Measurable x) : MP (fun a => A.exp (x a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.exp, Num.get_exp]; exact (getm hx).exp))
    fun _ _ => by simp [A.exp]

theorem mp_root {u : Q → Num ℝ} {k : Q → Num ℕ} (hu : Measurable u) (hk : Measurable k) :
    MP (fun a => A.root (u a) (k a)) :=
  MP.of_val (Num.measurable_of_get (by
      simp only [A.root, Num.get_root]
      exact (getm hu).pow (measurable_of_nat hk fun k => ((k : ℝ))⁻¹)))
    fun _ _ => by simp [A.root]

theorem mp_cast {k : Q → Num ℕ} (hk : Measurable k) : MP (fun a => A.cast (k a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.cast, Num.get_cast]; exact measurable_of_nat hk _))
    fun _ _ => by simp [A.cast]

theorem mp_ceil {x : Q → Num ℝ} (hx : Measurable x) : MP (fun a => A.ceil (x a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.ceil, Num.get_ceil]; exact (getm hx).nat_ceil))
    fun _ _ => by simp [A.ceil]

theorem mp_addN {x y : Q → Num ℕ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.add (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.add, Num.get_add]; exact measurable_of_nat₂ hx hy _))
    fun _ _ => by simp [A.add]

theorem mp_subN {x y : Q → Num ℕ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.sub (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.sub, Num.get_sub]; exact measurable_of_nat₂ hx hy _))
    fun _ _ => by simp [A.sub]

theorem mp_divN {x y : Q → Num ℕ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.div (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.div, Num.get_div]; exact measurable_of_nat₂ hx hy _))
    fun _ _ => by simp [A.div]

theorem mp_mulN {x y : Q → Num ℕ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.mul (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.mul, Num.get_mul]; exact measurable_of_nat₂ hx hy _))
    fun _ _ => by simp [A.mul]

theorem mp_leN {x y : Q → Num ℕ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.le (x a) (y a)) :=
  MP.of_val (by simp only [A.le, Num.val_le]; exact measurable_of_nat₂ hx hy _)
    fun _ _ => by simp [A.le]

theorem mp_ltN {x y : Q → Num ℕ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.lt (x a) (y a)) := by
  unfold A.lt
  exact MP.bind (mp_leN hy hx) (MP.pure ((measurable_of_countable (fun b : Bool => !b)).comp measurable_snd))

theorem mp_addZ {x y : Q → Num ℤ} (hx : Measurable x) (hy : Measurable y) :
    MP (fun a => A.add (x a) (y a)) :=
  MP.of_val (Num.measurable_of_get (by simp only [A.add, Num.get_add]; exact measurable_of_int₂ hx hy _))
    fun _ _ => by simp [A.add]

theorem mp_floor {x : Q → Num ℝ} (hx : Measurable x) : MP (fun a => floor (x a)) :=
  MP.of_val (Num.measurable_of_get (by
      simp only [floor, Charged.val_exchange, Num.get_lit]
      exact (getm hx).floor))
    fun _ _ => by simp [floor, opsTotal_exchange_relabel]

theorem mp_intCast {z : Q → Num ℤ} (hz : Measurable z) : MP (fun a => intCast (z a)) :=
  MP.of_val (Num.measurable_of_get (by
      simp only [intCast, Charged.val_exchange, Num.get_lit]
      exact measurable_of_int hz _))
    fun _ _ => by simp [intCast, opsTotal_exchange_relabel]

theorem mp_cell {α : Type} [MeasurableSpace α] {x : Q → α} (hx : Measurable x) :
    MP (fun a => A.cell (x a)) :=
  MP.of_val (by simpa [A.cell, ttc.Model.Operations.cell] using hx)
    fun _ _ => by simp [A.cell, ttc.Model.Operations.cell]

theorem mp_push {α : Type} [MeasurableSpace α] {xs : Q → List α} {x : Q → α}
    (hxs : Measurable xs) (hx : Measurable x) : MP (fun a => A.push (xs a) (x a)) :=
  MP.of_val (by
      simpa [A.push, ttc.Model.Operations.push] using List.measurable_append_singleton hxs hx)
    fun _ _ => by simp [A.push, ttc.Model.Operations.push]

end Ops

end ttc.Tape
