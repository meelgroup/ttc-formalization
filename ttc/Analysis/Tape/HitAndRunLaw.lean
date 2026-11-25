/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.HitAndRunValue
import ttc.Analysis.Tape.MeasTrees

/-!
# The sealed Hit-and-Run walk has arlib's law

On a bounded polytope, one step of the sealed walk (`hitAndRunStepT`) has the law of the
old model's step (`HalfspacePresentation.hitAndRunStepLaw`, `vlaw_hitAndRunStepT`), which is
arlib's lazy Hit-and-Run kernel inside the body; `T` steps from a point of the body have the
law of arlib's `T`-step chain (`vlaw_hitAndRunWalkT`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc.SealedRun (roundLaw tapeLaw)
open ArlibCommunity.Algorithms.CV18 (measurable_some)
open ArlibCommunity.Foundations.MarkovChainTheory (iterate)

variable {d : ℕ}

/-! ## Rounds of the tape -/

/-- The first round and the rest of the tape are independent. -/
theorem tapeLaw_map_head_tail {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {f : Round d → X} {g : Tape d → Y} (hf : Measurable f) (hg : Measurable g) :
    (tapeLaw d).map (fun t => (f (t 0), g t.tail)) =
      ((roundLaw d).map f).prod ((tapeLaw d).map g) := by
  rw [Measure.map_prod_map _ _ hf hg]
  conv_lhs => rw [tapeLaw_eq_map_cons]
  rw [Measure.map_map (show Measurable fun t : Tape d => (f (t 0), g t.tail) from
    (hf.comp (measurable_pi_apply 0)).prodMk (hg.comp measurable_tape_tail)) measurable_tape_cons]
  rfl

theorem tapeLaw_map_eval_zero : (tapeLaw d).map (fun t => t 0) = roundLaw d :=
  Measure.infinitePi_map_eval _ 0

/-- **The coin of the first round, the Gaussian vector of the second and the uniform
number of the third** are independent with their laws: the tape of one old-model step. -/
theorem tapeLaw_map_three :
    (tapeLaw d).map (fun t => ((t 0).1, (t 1).2.1, (t 2).2.2)) = hitAndRunTape d := by
  have h2 : (tapeLaw d).map (fun t => ((t 0).2.1, (t.tail 0).2.2)) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).prod uniformUnit := by
    rw [tapeLaw_map_head_tail (f := fun r : Round d => r.2.1) (g := fun t : Tape d => (t 0).2.2)
      (measurable_fst.comp measurable_snd)
      ((measurable_snd.comp measurable_snd).comp (measurable_pi_apply 0)),
      roundLaw_map_gaussian,
      show (fun t : Tape d => (t 0).2.2) = (fun r : Round d => r.2.2) ∘ (fun t => t 0) from rfl,
      ← Measure.map_map (g := fun r : Round d => r.2.2) (f := fun t : Tape d => t 0)
        (measurable_snd.comp measurable_snd) (measurable_pi_apply 0),
      tapeLaw_map_eval_zero, roundLaw_map_unit]
  have hg : Measurable fun t : Tape d => ((t 0).2.1, (t.tail 0).2.2) :=
    ((measurable_fst.comp measurable_snd).comp (measurable_pi_apply 0)).prodMk
      ((measurable_snd.comp measurable_snd).comp ((measurable_pi_apply 0).comp measurable_tape_tail))
  rw [show (fun t : Tape d => ((t 0).1, (t 1).2.1, (t 2).2.2)) =
      fun t => ((t 0).1, (fun t' : Tape d => ((t' 0).2.1, (t'.tail 0).2.2)) t.tail) from rfl,
    tapeLaw_map_head_tail measurable_fst hg, roundLaw_map_coin, h2]
  rfl

/-! ## Optional values -/

theorem measurable_optionMap {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) : Measurable (Option.map f) := by
  have : Option.map f = fun o : Option α => match o with
      | none => none
      | some x => some (f x) := by
    funext o; cases o <;> rfl
  rw [this]
  exact ArlibCommunity.Algorithms.CV18.Measurable.optionElim _ (measurable_some.comp hf)

/-! ## One step -/

/-- **One step of the sealed walk has the old model's step law** at every point, on a
bounded body. -/
theorem vlaw_hitAndRunStepT (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (hK : Bornology.IsBounded (bodyOf r a β')) (hne : (bodyOf r a β').Nonempty)
    (x : NumPoint d) (b : ℕ) :
    (vlaw (hitAndRunStepT r a β' x) b).map (Option.map toPt) =
      ((presOf r a β').hitAndRunStepLaw (toPt x)).map some := by
  set H := presOf r a β'
  have hm : Measurable fun t => outcome (exec (hitAndRunStepT r a β' x) b t) :=
    (mf_hitAndRunStep (Q := Unit) r a β' (x := fun _ => x) measurable_const).outcome () b
  have hF : Measurable fun ω : Bool × EuclideanSpace ℝ (Fin d) × ℝ =>
      if ω.1 then toPt x else H.move (toPt x) ω.2.1 ω.2.2 :=
    Measurable.ite (measurable_fst (measurableSet_singleton true)) measurable_const
      ((ttc.HitAndRunLaw.measurable_move H (toPt x)).comp measurable_snd)
  have h3 : Measurable fun t : Tape d => ((t 0).1, (t 1).2.1, (t 2).2.2) :=
    (measurable_fst.comp (measurable_pi_apply 0)).prodMk
      (((measurable_fst.comp measurable_snd).comp (measurable_pi_apply 1)).prodMk
        ((measurable_snd.comp measurable_snd).comp (measurable_pi_apply 2)))
  have hfun : (fun t => Option.map toPt (outcome (exec (hitAndRunStepT r a β' x) b t)).1) =
      (some ∘ fun ω : Bool × EuclideanSpace ℝ (Fin d) × ℝ =>
        if ω.1 then toPt x else H.move (toPt x) ω.2.1 ω.2.2) ∘
        fun t : Tape d => ((t 0).1, (t 1).2.1, (t 2).2.2) := by
    funext t
    exact exec_hitAndRunStepT r a β' hK hne x b t
  have hstep : H.hitAndRunStepLaw (toPt x) = (hitAndRunTape d).map fun ω =>
      if ω.1 then toPt x else H.move (toPt x) ω.2.1 ω.2.2 := by
    rw [HalfspacePresentation.hitAndRunStepLaw]
    congr 1
    funext ω
    exact H.hitAndRunStep_value (toPt x) ω.1 ω.2.1 ω.2.2
  rw [vlaw, ← tapeLaw_map_exec _ b hm, Measure.map_map measurable_fst hm,
    Measure.map_map (measurable_optionMap measurable_toPt) (measurable_fst.comp hm)]
  change (tapeLaw d).map (fun t => Option.map toPt (outcome (exec (hitAndRunStepT r a β' x) b t)).1) = _
  rw [hfun, ← Measure.map_map (measurable_some.comp hF) h3, tapeLaw_map_three, hstep,
    Measure.map_map measurable_some hF]

end ttc.Tape

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc.SealedRun (roundLaw tapeLaw)
open ArlibCommunity.Algorithms.CV18 (measurable_some)
open ArlibCommunity.Foundations.MarkovChainTheory (iterate)

variable {d : ℕ}

/-! ## Tree algebra -/

namespace Tree

variable {n : ℕ} {α β γ : Type}

theorem bind_assoc (p : Tree n α) (f : α → Tree n β) (g : β → Tree n γ) :
    (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  induction p with
  | pure a => rfl
  | fail => rfl
  | step c k ih => exact congrArg (Tree.step c) (funext ih)
  | coin k ih => exact congrArg Tree.coin (funext ih)
  | unit k ih => exact congrArg Tree.unit (funext ih)
  | gaussian k ih => exact congrArg Tree.gaussian (funext ih)
  | poisson r k ih => exact congrArg (Tree.poisson r) (funext ih)
  | binom N k ih => exact congrArg (Tree.binom N) (funext ih)
  | setBudget c k ih => exact congrArg (Tree.setBudget c) ih
  | spend k ih => exact congrArg Tree.spend (funext ih)

theorem free_loopRounds {body : β → Tree n (β ⊕ γ)} (hb : ∀ y, Free (body y)) :
    ∀ (k : ℕ) (y : β), Free (loopRounds body k y)
  | 0, _ => trivial
  | k + 1, y => Free.bind (hb y) fun r => by
      rcases r with y' | c
      · exact free_loopRounds hb k y'
      · trivial

variable [MeasurableSpace α] [MeasurableSpace β]

theorem vlaw_step {δ : Type} (c : Prog δ) (k : δ → Tree n α) (b : ℕ) :
    vlaw (Tree.step c k) b = vlaw (k c.val) b := by
  simp only [vlaw, law]
  rw [Measure.map_map measurable_fst (measurable_addOps _)]
  rfl

/-- Mapping the result. -/
theorem vlaw_bind_pure {p : Tree n α} (hp : Free p) (h : α → β) (hh : Measurable h) (b : ℕ)
    (hm : Measurable fun t => outcome (exec p b t)) :
    vlaw (p.bind fun a => Tree.pure (h a)) b = (vlaw p b).map (Option.map h) := by
  rw [vlaw_bind (MeasFam.pure hh) hp b hm]
  have : (fun o : Option α => o.elim (Measure.dirac none) fun a => vlaw (Tree.pure (n := n) (h a)) b) =
      fun o => Measure.dirac (Option.map h o) := by
    funext o
    cases o <;> simp [vlaw_pure]
  rw [this, Measure.bind_dirac_eq_map _ (measurable_optionMap hh)]

end Tree

/-! ## Iterating a kernel from a point -/

section Iterate

variable {Ω : Type} [MeasurableSpace Ω] (P : Kernel Ω Ω)

theorem measurable_iterate_dirac : ∀ k : ℕ, Measurable fun z : Ω => iterate P (Measure.dirac z) k
  | 0 => Measure.measurable_dirac
  | k + 1 => (Measure.measurable_bind' P.measurable).comp (measurable_iterate_dirac k)

/-- The chain from a law is the chain from each of its points, averaged. -/
theorem iterate_eq_bind (μ : Measure Ω) :
    ∀ k : ℕ, iterate P μ k = μ.bind fun z => iterate P (Measure.dirac z) k
  | 0 => (Measure.bind_dirac).symm
  | k + 1 => by
      show (iterate P μ k).bind P = _
      rw [iterate_eq_bind μ k, Measure.bind_bind (measurable_iterate_dirac P k).aemeasurable
        P.measurable.aemeasurable]
      rfl

/-- One step from `y`, then the chain. -/
theorem iterate_dirac_succ (y : Ω) (k : ℕ) :
    iterate P (Measure.dirac y) (k + 1) = (P y).bind fun z => iterate P (Measure.dirac z) k := by
  rw [Nat.add_comm, ArlibCommunity.Foundations.MarkovChainTheory.iterate_add,
    ArlibCommunity.Foundations.MarkovChainTheory.iterate_one,
    ArlibCommunity.Foundations.MarkovChainTheory.step, Measure.dirac_bind P.measurable,
    iterate_eq_bind]

end Iterate

/-! ## The walk -/

/-- One round of the walk's loop. -/
def walkBodyT (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ) (y : NumPoint d) :
    Tree d (NumPoint d ⊕ Empty) :=
  (hitAndRunStepT r a β' y).bind fun y' => .pure (.inl y')

theorem free_hitAndRunStepT (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (x : NumPoint d) : Free (hitAndRunStepT r a β' x) := by
  refine Free.bind free_coinT fun stay => free_ite _ (free_pure _) ?_
  refine Free.bind free_gaussianT fun g => Free.bind (free_compute _) fun θ =>
    Free.bind (free_compute _) fun ends => ?_
  rcases ends with ⟨_ | lo, _ | hi⟩
  · exact free_pure _
  · exact free_pure _
  · exact free_pure _
  · exact Free.bind (free_compute _) fun ok => free_ite _
      (Free.bind free_unitT fun u => free_compute _) (free_pure _)

theorem free_walkBodyT (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ) (y : NumPoint d) :
    Free (walkBodyT r a β' y) :=
  Free.bind (free_hitAndRunStepT r a β' y) fun _ => free_pure _

theorem mf_walkBodyT {Q : Type} [MeasurableSpace Q] (r : ℕ) (a : Fin r → NumPoint d)
    (β' : Fin r → Num ℝ) : MeasFam fun p : Q × NumPoint d => walkBodyT r a β' p.2 :=
  MeasFam.bind' (mf_hitAndRunStep r a β' measurable_snd)
    (MeasFam.pure (g := fun p : (Q × NumPoint d) × NumPoint d => (Sum.inl p.2 : _ ⊕ Empty))
      (measurable_inl.comp measurable_snd))

theorem mf_walkRounds (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ) (k : ℕ) :
    MeasFam fun y : NumPoint d => loopRounds (walkBodyT r a β') k y :=
  (MeasFam.loopRounds (A := Unit) (body := fun _ => walkBodyT r a β') (mf_walkBodyT r a β') k).comp
    (φ := fun y : NumPoint d => ((), y)) (measurable_const.prodMk measurable_id)

/-- The step's result law, held: the old step law, sealed. -/
theorem vlaw_hitAndRunStepT' (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (hK : Bornology.IsBounded (bodyOf r a β')) (hne : (bodyOf r a β').Nonempty)
    (x : NumPoint d) (b : ℕ) :
    vlaw (hitAndRunStepT r a β' x) b =
      ((presOf r a β').hitAndRunStepLaw (toPt x)).map fun z => some (ofPt z) := by
  have h := congrArg (Measure.map (Option.map ofPt)) (vlaw_hitAndRunStepT r a β' hK hne x b)
  rw [Measure.map_map (measurable_optionMap measurable_ofPt) (measurable_optionMap measurable_toPt),
    Measure.map_map (measurable_optionMap measurable_ofPt) measurable_some] at h
  have hid : Option.map ofPt ∘ Option.map (toPt (d := d)) = id := by
    funext o; cases o <;> simp
  rw [hid, Measure.map_id] at h
  rw [h]
  rfl

/-- The walk's rounds, as points. -/
def walkView : Option (NumPoint d ⊕ Empty) → Option (EuclideanSpace ℝ (Fin d)) :=
  Option.map (Sum.elim toPt Empty.elim)

theorem measurable_walkView : Measurable (walkView (d := d)) :=
  measurable_optionMap (measurable_toPt.sumElim measurable_from_top)

open ttc.HitAndRunLaw in
/-- **`k` rounds of the sealed walk from a point of a bounded body have the law of arlib's
`k`-step lazy Hit-and-Run chain.** -/
theorem vlaw_walkRounds [NeZero d] (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (hK : Bornology.IsBounded (bodyOf r a β')) (b : ℕ) :
    ∀ (k : ℕ) (y : NumPoint d), toPt y ∈ bodyOf r a β' →
      (vlaw (loopRounds (walkBodyT r a β') k y) b).map walkView =
        (iterate (lazyKernel (presOf r a β')) (Measure.dirac (toPt y)) k).map some
  | 0, y, _ => by
      show (vlaw (Tree.pure (Sum.inl y)) b).map walkView = _
      rw [vlaw_pure, Measure.map_dirac' measurable_walkView]
      show _ = Measure.map some (Measure.dirac (toPt y))
      rw [Measure.map_dirac' measurable_some]
      rfl
  | k + 1, y, hy => by
      set H := presOf r a β'
      have hne : (bodyOf r a β').Nonempty := ⟨_, hy⟩
      have hloop : loopRounds (walkBodyT r a β') (k + 1) y =
          (hitAndRunStepT r a β' y).bind fun y' => loopRounds (walkBodyT r a β') k y' := by
        show ((hitAndRunStepT r a β' y).bind fun y' => Tree.pure (Sum.inl y')).bind _ = _
        rw [Tree.bind_assoc]
        rfl
      have hm : Measurable fun t => outcome (exec (hitAndRunStepT r a β' y) b t) :=
        (mf_hitAndRunStep (Q := Unit) r a β' (x := fun _ => y) measurable_const).outcome () b
      have hmf := mf_walkRounds r a β' k
      have hK' := (hmf.measurable_vlaw b)
      have hker : Measurable fun z : EuclideanSpace ℝ (Fin d) =>
          vlaw (loopRounds (walkBodyT r a β') k (ofPt z)) b := hK'.comp measurable_ofPt
      have hstep : H.hitAndRunStepLaw (toPt y) = lazyKernel H (toPt y) :=
        hitAndRunStepLaw_eq H (toPt y) hy
      rw [hloop, vlaw_bind hmf (free_hitAndRunStepT r a β' y) b hm,
        vlaw_hitAndRunStepT' r a β' hK hne y b,
        Measure.bind_map (f := fun z => some (ofPt z)) (measurable_some.comp measurable_ofPt).aemeasurable
          (measurable_optionKernel hK').aemeasurable]
      simp only [Function.comp_def, Option.elim]
      rw [Measure.map_bind hker.aemeasurable measurable_walkView.aemeasurable, hstep]
      have hae : ∀ᵐ z ∂lazyKernel H (toPt y), z ∈ bodyOf r a β' :=
        ae_iff.mpr (lazyKernel_compl_body H (toPt y) hK hy)
      have hcongr : (fun z => (vlaw (loopRounds (walkBodyT r a β') k (ofPt z)) b).map walkView)
          =ᵐ[lazyKernel H (toPt y)]
          fun z => (iterate (lazyKernel H) (Measure.dirac z) k).map some :=
        hae.mono fun z hz => by
          have := vlaw_walkRounds r a β' hK b k (ofPt z) (by rwa [toPt_ofPt])
          rwa [toPt_ofPt] at this
      rw [Measure.bind_congr_right hcongr, iterate_dirac_succ, Measure.map_bind
          (measurable_iterate_dirac _ k).aemeasurable measurable_some.aemeasurable]

open ttc.HitAndRunLaw in
/-- **`T` steps of the sealed walk from a point of a bounded body have the law of arlib's
`T`-step lazy Hit-and-Run chain** (`T` the held step count). -/
theorem vlaw_hitAndRunWalkT [NeZero d] (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (hK : Bornology.IsBounded (bodyOf r a β')) (steps : Num ℕ) (x : NumPoint d)
    (hx : toPt x ∈ bodyOf r a β') (b : ℕ) :
    (vlaw (hitAndRunWalkT r a β' steps x) b).map (Option.map toPt) =
      (iterate (lazyKernel (presOf r a β')) (Measure.dirac (toPt x)) steps.get).map some := by
  have hloop : MeasFam fun _ : Unit => loopTree steps (walkBodyT r a β') x :=
    MeasFam.loopTree (count := fun _ => steps) measurable_const (mf_walkBodyT r a β')
      measurable_const
  have hfree : Free (loopTree steps (walkBodyT r a β') x) :=
    Tree.free_loopRounds (free_walkBodyT r a β') _ x
  have hel : Measurable fun res : NumPoint d ⊕ Empty => Sum.elim id Empty.elim res :=
    measurable_id.sumElim measurable_from_top
  rw [show hitAndRunWalkT r a β' steps x = (loopTree steps (walkBodyT r a β') x).bind
      fun res => Tree.pure (Sum.elim id Empty.elim res) from rfl,
    Tree.vlaw_bind_pure hfree _ hel b (hloop.outcome () b),
    Measure.map_map (measurable_optionMap measurable_toPt) (measurable_optionMap hel)]
  have hv : Option.map toPt ∘ Option.map (Sum.elim id Empty.elim) = walkView (d := d) := by
    funext o
    rcases o with _ | (y | e)
    · rfl
    · rfl
    · exact e.elim
  rw [hv, loopTree, Tree.vlaw_step]
  exact vlaw_walkRounds r a β' hK b steps.get x hx

end ttc.Tape
