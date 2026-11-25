/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Meas

/-!
# The law of a sequence of trees

The law of `p.bind f` is the law of `p` followed by the law of `f` at `p`'s result
(`Tree.law_bind`): if `p` stops, so does `p.bind f`; otherwise `f a` runs with the calls
`p` left, and the operations add up (`Tree.cont`).  This lets a tree's law be computed one
piece at a time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open ttc.Model.Operations
open ttc.SealedRun (roundLaw tapeLaw)
open ArlibCommunity.Algorithms.CV18 (measurable_some)

namespace Tree

variable {n : ℕ} {β γ : Type} [MeasurableSpace β] [MeasurableSpace γ]

theorem measurable_outcome :
    Measurable (outcome : Option β × ℕ × ℕ × Tape n → Outcome β) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst)

/-! ## A tree's law depends measurably on its argument -/

/-- When a family of trees runs measurably in its argument and the tape, its law is a
measurable function of the argument. -/
theorem measurable_law_of {X : Type} [MeasurableSpace X] (k : X → Tree n β) (b : X → ℕ)
    (hH : Measurable fun p : X × Tape n => outcome (exec (k p.1) (b p.1) p.2)) :
    Measurable fun x => law (k x) (b x) := by
  have hsec : ∀ x, Measurable fun t => outcome (exec (k x) (b x) t) := fun x =>
    hH.comp (measurable_const.prodMk measurable_id)
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have : ∀ x, law (k x) (b x) S = tapeLaw n (Prod.mk x ⁻¹'
      ((fun p : X × Tape n => outcome (exec (k p.1) (b p.1) p.2)) ⁻¹' S)) := fun x =>
    (tapeLaw_preimage_exec (k x) (b x) (hsec x) hS).symm
  simp_rw [this]
  exact measurable_measure_prodMk_left (hH hS)

/-- The law of a measurable family, as a function of the argument and the calls left. -/
theorem MeasFam.measurable_law {A : Type} [MeasurableSpace A] {f : A → Tree n β}
    (hf : MeasFam f) : Measurable fun p : A × ℕ => law (f p.1) p.2 := by
  refine measurable_law_of (fun p : A × ℕ => f p.1) Prod.snd ?_
  exact measurable_outcome.comp ((show Measurable _ from hf).comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))

/-- Reading a component of the first round: the run is measurable in the value read and
the rest of the tape together. -/
theorem measurable_joint_of_draw {X : Type} [MeasurableSpace X] (π : Round n → X)
    (σ : X → Round n) (hσ : Measurable σ) (hσπ : ∀ x, π (σ x) = x) (j b : ℕ)
    (k : X → Tree n β)
    (hk : Measurable fun t : Tape n => addOps j (outcome (exec (k (π (t 0))) b t.tail))) :
    Measurable fun p : X × Tape n => outcome (exec (k p.1) b p.2) := by
  have hk' : Measurable fun t : Tape n => outcome (exec (k (π (t 0))) b t.tail) := by
    have : (fun t : Tape n => outcome (exec (k (π (t 0))) b t.tail)) =
        (fun r : Outcome β => (r.1, r.2.1 - j, r.2.2)) ∘
          fun t => addOps j (outcome (exec (k (π (t 0))) b t.tail)) := by
      funext t
      simp [addOps]
    rw [this]
    exact (measurable_fst.prodMk ((measurable_snd.fst.sub_const j).prodMk
      measurable_snd.snd)).comp hk
  have : (fun p : X × Tape n => outcome (exec (k p.1) b p.2)) =
      (fun t : Tape n => outcome (exec (k (π (t 0))) b t.tail)) ∘
        fun p : X × Tape n => cons (σ p.1) p.2 := by
    funext p
    simp only [Function.comp_apply, cons_zero, tail_cons, hσπ]
  rw [this]
  exact hk'.comp (measurable_tape_cons.comp ((hσ.comp measurable_fst).prodMk measurable_snd))

/-- Undoing `addOps j` keeps measurability. -/
theorem measurable_of_addOps {X : Type} [MeasurableSpace X] {g : X → Outcome β} (j : ℕ)
    (hg : Measurable fun x => addOps j (g x)) : Measurable g := by
  have : g = (fun r : Outcome β => (r.1, r.2.1 - j, r.2.2)) ∘ fun x => addOps j (g x) := by
    funext x
    simp [addOps]
  rw [this]
  exact (measurable_fst.prodMk ((measurable_snd.fst.sub_const j).prodMk
    measurable_snd.snd)).comp hg

/-! ## The continuation -/

/-- What follows an outcome of `p` in `p.bind f`: a stop stays a stop; a result `a` runs
`f a` with the calls left, adding the operations already spent. -/
def cont (f : β → Tree n γ) (o : Outcome β) : Measure (Outcome γ) :=
  o.1.elim (Measure.dirac (none, o.2.1, o.2.2)) fun a => (law (f a) o.2.2).map (addOps o.2.1)

theorem measurable_cont {f : β → Tree n γ} (hf : MeasFam f) : Measurable (cont f) := by
  have hL := hf.measurable_law
  refine measurable_from_prod_countable_left fun mb => ?_
  have : (fun o : Option β => cont f (o, mb)) =
      Sum.elim (fun _ : Unit => Measure.dirac ((none, mb.1, mb.2) : Outcome γ))
        (fun a => (law (f a) mb.2).map (addOps mb.1)) ∘
        ArlibCommunity.Algorithms.CV18.optionToSum := by
    funext o
    cases o <;> rfl
  rw [this]
  refine Measurable.comp (Measurable.sumElim measurable_const ?_)
    ArlibCommunity.Algorithms.CV18.measurable_optionToSum
  exact (Measure.measurable_map _ (measurable_addOps _)).comp
    (hL.comp (measurable_id.prodMk measurable_const))

omit [MeasurableSpace β] in
theorem addOps_addOps (i j : ℕ) (o : Outcome β) : addOps i (addOps j o) = addOps (i + j) o := by
  simp [addOps, add_assoc]

omit [MeasurableSpace β] in
theorem cont_addOps (f : β → Tree n γ) (j : ℕ) (o : Outcome β) :
    cont f (addOps j o) = (cont f o).map (addOps j) := by
  obtain ⟨_ | a, m, b'⟩ := o
  · simp only [cont, addOps, Option.elim]
    rw [Measure.map_dirac' (measurable_addOps j)]
    rfl
  · simp only [cont, addOps, Option.elim]
    rw [Measure.map_map (measurable_addOps j) (measurable_addOps m)]
    congr 1
    funext o
    simp [addOps, add_assoc]

/-- Adding operations commutes with continuing. -/
theorem map_bind_cont {f : β → Tree n γ} (hc : Measurable (cont f)) (L : Measure (Outcome β))
    (j : ℕ) : (L.bind (cont f)).map (addOps j) = (L.map (addOps j)).bind (cont f) := by
  rw [Measure.map_bind hc.aemeasurable (measurable_addOps j).aemeasurable,
    Measure.bind_map (measurable_addOps j).aemeasurable hc.aemeasurable]
  simp_rw [cont_addOps]

/-- A draw, then a continuation. -/
theorem bind_draw {X : Type} [MeasurableSpace X] {f : β → Tree n γ} (hc : Measurable (cont f))
    (μ : Measure X) {K : X → Measure (Outcome β)} (hK : Measurable K) (j : ℕ) :
    μ.bind (fun x => ((K x).bind (cont f)).map (addOps j)) =
      (μ.bind fun x => (K x).map (addOps j)).bind (cont f) := by
  rw [Measure.bind_bind (f := fun x => (K x).map (addOps j))
    ((Measure.measurable_map _ (measurable_addOps j)).comp hK).aemeasurable hc.aemeasurable]
  simp_rw [map_bind_cont hc]

/-! ## The law of `p.bind f` -/

/-- **The law of a sequence**: run `p`, then continue with `f` at its result. -/
theorem law_bind {f : β → Tree n γ} (hf : MeasFam f) (p : Tree n β) (b : ℕ)
    (hp : Measurable fun t => outcome (exec p b t)) :
    law (p.bind f) b = (law p b).bind (cont f) := by
  have hc := measurable_cont hf
  induction p generalizing b with
  | pure a =>
      show law (f a) b = _
      rw [law, Measure.dirac_bind hc]
      simp only [cont, Option.elim]
      have : addOps (α := γ) 0 = id := by funext o; simp [addOps]
      rw [this, Measure.map_id]
  | fail =>
      show Measure.dirac _ = _
      rw [law, Measure.dirac_bind hc]
      rfl
  | step c k ih =>
      show (law ((k c.val).bind f) b).map _ = _
      have hk := measurable_of_addOps (g := fun t => outcome (exec (k c.val) b t)) _ hp
      rw [ih c.val b hk, law, map_bind_cont hc]
  | coin k ih =>
      show fairCoinLaw.bind (fun x => (law ((k x).bind f) b).map (addOps 1)) = _
      have hH := measurable_joint_of_draw (fun r => r.1) (fun x => (x, 0, 0))
        (measurable_id.prodMk measurable_const) (fun _ => rfl) 1 b k hp
      have hsec : ∀ x, Measurable fun t => outcome (exec (k x) b t) := fun x =>
        hH.comp (measurable_const.prodMk measurable_id)
      simp_rw [fun x => ih x b (hsec x)]
      exact bind_draw hc _ (measurable_law_of k (fun _ => b) hH) 1
  | unit k ih =>
      show uniformUnit.bind (fun x => (law ((k x).bind f) b).map (addOps 1)) = _
      have hH := measurable_joint_of_draw (fun r => r.2.2) (fun v => (false, 0, v))
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)) (fun _ => rfl) 1 b k hp
      have hsec : ∀ x, Measurable fun t => outcome (exec (k x) b t) := fun x =>
        hH.comp (measurable_const.prodMk measurable_id)
      simp_rw [fun x => ih x b (hsec x)]
      exact bind_draw hc _ (measurable_law_of k (fun _ => b) hH) 1
  | gaussian k ih =>
      show (ProbabilityTheory.stdGaussian _).bind
        (fun x => (law ((k x).bind f) b).map (addOps n)) = _
      have hH := measurable_joint_of_draw (fun r => r.2.1) (fun g => (false, g, 0))
        (measurable_const.prodMk (measurable_id.prodMk measurable_const)) (fun _ => rfl) n b k hp
      have hsec : ∀ x, Measurable fun t => outcome (exec (k x) b t) := fun x =>
        hH.comp (measurable_const.prodMk measurable_id)
      simp_rw [fun x => ih x b (hsec x)]
      exact bind_draw hc _ (measurable_law_of k (fun _ => b) hH) n
  | poisson rate k ih =>
      show uniformUnit.bind
        (fun u => (law ((k (poissonQuantile (Real.toNNReal rate.get) u)).bind f) b).map
          (addOps 1)) = _
      have hH := measurable_joint_of_draw (fun r => r.2.2) (fun v => (false, 0, v))
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)) (fun _ => rfl) 1 b
        (fun u => k (poissonQuantile (Real.toNNReal rate.get) u)) hp
      have hsec : ∀ u, Measurable fun t =>
          outcome (exec (k (poissonQuantile (Real.toNNReal rate.get) u)) b t) := fun u =>
        hH.comp (measurable_const.prodMk measurable_id)
      simp_rw [fun u => ih _ b (hsec u)]
      exact bind_draw hc _ (measurable_law_of _ (fun _ => b) hH) 1
  | binom N k ih =>
      show uniformUnit.bind
        (fun u => (law ((k (binomialHalfQuantile N.get u)).bind f) b).map (addOps 1)) = _
      have hH := measurable_joint_of_draw (fun r => r.2.2) (fun v => (false, 0, v))
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)) (fun _ => rfl) 1 b
        (fun u => k (binomialHalfQuantile N.get u)) hp
      have hsec : ∀ u, Measurable fun t =>
          outcome (exec (k (binomialHalfQuantile N.get u)) b t) := fun u =>
        hH.comp (measurable_const.prodMk measurable_id)
      simp_rw [fun u => ih _ b (hsec u)]
      exact bind_draw hc _ (measurable_law_of _ (fun _ => b) hH) 1
  | setBudget c k ih =>
      show (law (k.bind f) c.get).map _ = _
      have hk := measurable_of_addOps (g := fun t => outcome (exec k c.get t)) _ hp
      rw [ih c.get hk, law, map_bind_cont hc]
  | spend k ih =>
      cases b with
      | zero => exact ih false 0 hp
      | succ b => exact ih true b hp

end Tree

end ttc.Tape
