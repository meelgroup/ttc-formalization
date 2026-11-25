/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.MeasHelpers
import ttc.Analysis.Tape.CV18Trees

/-!
# Measurable families of trees: the remaining rules

The rules of `Analysis/Tape/Meas.lean`, completed for the nodes and combinators the
program's trees use: steps whose computation does not depend on the argument, steps with
measurable value and count (`MP`), every read of the tape (the Poisson and binomial
quantiles included), the query cap, recovery (`orElse`), loops with a fixed or a random
count, folds over a fixed or a random list, and case splits.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Set

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ArlibCommunity.Algorithms.CV18 (measurable_some)

/-! ## Quantiles -/

/-- `sInf` of a family of measurable sets of naturals is measurable. -/
theorem measurable_nat_sInf {X : Type} [MeasurableSpace X] {P : ℕ → X → Prop}
    (hP : ∀ k, MeasurableSet {x | P k x}) : Measurable fun x => sInf {k | P k x} := by
  refine measurable_to_countable' fun j => ?_
  have : (fun x => sInf {k | P k x}) ⁻¹' {j} =
      ({x | P j x} ∩ ⋂ k ∈ Finset.range j, {x | P k x}ᶜ) ∪
        (if j = 0 then ⋂ k, {x | P k x}ᶜ else ∅) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_iInter,
      Finset.mem_range, mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      by_cases hne : ∃ k, P k x
      · left
        have hmem : P (sInf {k | P k x}) x := Nat.sInf_mem hne
        rw [h] at hmem
        exact ⟨hmem, fun k hk hPk => absurd (h ▸ Nat.sInf_le hPk) (by omega)⟩
      · right
        push Not at hne
        have hempty : {k | P k x} = ∅ := Set.eq_empty_of_forall_notMem fun k hk => hne k hk
        rw [hempty, Nat.sInf_empty] at h
        subst h
        simp only [ite_true, mem_iInter]
        exact fun k => hne k
    · rintro (⟨hj, hlt⟩ | h)
      · refine le_antisymm (Nat.sInf_le hj) ?_
        by_contra hlt'
        push Not at hlt'
        exact hlt _ hlt' (Nat.sInf_mem (s := {k | P k x}) ⟨j, hj⟩)
      · split_ifs at h with hj0
        · subst hj0
          have hempty : {k | P k x} = ∅ :=
            Set.eq_empty_of_forall_notMem fun k hk => (mem_iInter.mp h k) hk
          rw [hempty, Nat.sInf_empty]
        · exact absurd h (Set.notMem_empty x)
  rw [this]
  refine ((hP j).inter (MeasurableSet.biInter (Set.to_countable _) fun k _ => (hP k).compl)).union ?_
  split_ifs
  · exact MeasurableSet.iInter fun k => (hP k).compl
  · exact MeasurableSet.empty

theorem poisson_cdf (r : NNReal) (k : ℕ) :
    (ProbabilityTheory.poissonMeasure r).real (Set.Iic k) =
      ∑ i ∈ Finset.range (k + 1), Real.exp (-r) * (r : ℝ) ^ i / (i.factorial : ℝ) := by
  have hset : (Set.Iic k : Set ℕ) = ↑(Finset.range (k + 1)) := by
    ext i; simp
  rw [hset, ← MeasureTheory.sum_measureReal_singleton]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ProbabilityTheory.poissonMeasure_real_singleton r i

theorem measurable_poissonQuantile :
    Measurable fun p : ℝ × ℝ => poissonQuantile (Real.toNNReal p.1) p.2 := by
  unfold poissonQuantile
  refine measurable_nat_sInf fun k => ?_
  simp_rw [poisson_cdf]
  have hc : Continuous fun p : ℝ × ℝ => ∑ i ∈ Finset.range (k + 1),
      Real.exp (-(Real.toNNReal p.1 : ℝ)) * ((Real.toNNReal p.1 : ℝ)) ^ i / (i.factorial : ℝ) := by
    fun_prop
  exact measurableSet_le measurable_snd hc.measurable

theorem measurable_binomialHalfQuantile :
    Measurable fun p : ℕ × ℝ => binomialHalfQuantile p.1 p.2 := by
  refine measurable_from_prod_countable_right fun N => ?_
  unfold binomialHalfQuantile
  refine measurable_nat_sInf fun k => ?_
  dsimp only
  exact measurableSet_le measurable_id measurable_const

/-! ## Rules -/

namespace Tree

variable {d : ℕ} {A β γ : Type} [MeasurableSpace A] [MeasurableSpace β] [MeasurableSpace γ]

/-- A step whose computation does not depend on the argument. -/
theorem MeasFam.stepConst {δ : Type} (c : Prog δ) {k : A → δ → Tree d β}
    (hk : MeasFam fun a => k a c.val) : MeasFam fun a => Tree.step c (k a) := by
  have hr : Measurable fun p : A × ℕ × Tape d => exec (k p.1 c.val) p.2.1 p.2.2 := hk
  exact hr.fst.prodMk ((measurable_const.add hr.snd.fst).prodMk hr.snd.snd)

/-- Charged arithmetic that does not depend on the argument, then a continuation. -/
theorem MeasFam.computeConst {δ : Type} (c : Prog δ) {k : A → δ → Tree d β}
    (hk : MeasFam fun a => k a c.val) : MeasFam fun a => (compute c).bind (k a) :=
  MeasFam.stepConst c hk

/-- Measurable charged arithmetic, then a continuation. -/
theorem MeasFam.compute {δ : Type} [MeasurableSpace δ] {c : A → Prog δ} (hc : MP c)
    {k : A → δ → Tree d β} (hk : MeasFam fun p : A × δ => k p.1 p.2) :
    MeasFam fun a => (Tree.compute (c a)).bind (k a) :=
  MeasFam.step (c := c) hc.1 hc.2 (k := fun p => k p.1 p.2) hk

/-- Sequencing, with the continuation curried. -/
theorem MeasFam.bind' [Inhabited β] {f : A → Tree d β} {k : A → β → Tree d γ}
    (hf : MeasFam f) (hk : MeasFam fun p : A × β => k p.1 p.2) :
    MeasFam fun a => (f a).bind (k a) :=
  MeasFam.bind (h := fun p => k p.1 p.2) hf hk

theorem MeasFam.const {p : Tree d β} (hp : Measurable fun q : ℕ × Tape d => exec p q.1 q.2) :
    MeasFam fun _ : A => p :=
  hp.comp measurable_snd

theorem MeasFam.coinT {k : A → Bool → Tree d β} (hk : MeasFam fun p : A × Bool => k p.1 p.2) :
    MeasFam fun a => Tree.coinT.bind (k a) :=
  MeasFam.coin (k := fun p => k p.1 p.2) hk

theorem measurable_sealDraw {α : Type} [MeasurableSpace α] :
    Measurable fun a : α => (sealDraw a).val :=
  Num.measurable_of_get (by simp only [get_sealDraw]; exact measurable_id')

theorem MeasFam.unitT {k : A → Num ℝ → Tree d β}
    (hk : MeasFam fun p : A × Num ℝ => k p.1 p.2) : MeasFam fun a => Tree.unitT.bind (k a) :=
  MeasFam.unit (k := fun p => k p.1 (sealDraw p.2).val)
    (hk.comp (measurable_fst.prodMk (measurable_sealDraw.comp measurable_snd)))

theorem measurable_sealVector :
    Measurable fun g : EuclideanSpace ℝ (Fin d) => (sealVector d (WithLp.ofLp g)).val := by
  refine measurable_pi_iff.mpr fun i => Num.measurable_of_get ?_
  simp only [get_sealVector]
  exact (measurable_pi_apply i).comp (PiLp.continuous_ofLp 2 _).measurable

theorem MeasFam.gaussianT {k : A → NumPoint d → Tree d β}
    (hk : MeasFam fun p : A × NumPoint d => k p.1 p.2) : MeasFam fun a => Tree.gaussianT.bind (k a) :=
  MeasFam.gaussian (k := fun p => k p.1 (sealVector d (WithLp.ofLp p.2)).val)
    (hk.comp (measurable_fst.prodMk (measurable_sealVector.comp measurable_snd)))

theorem MeasFam.poissonT {rate : A → Num ℝ} (hr : Measurable rate) {k : A → Num ℕ → Tree d β}
    (hk : MeasFam fun p : A × Num ℕ => k p.1 p.2) :
    MeasFam fun a => (Tree.poissonT (rate a)).bind (k a) := by
  have hq : Measurable fun p : A × ℕ × Tape d =>
      (sealDraw (poissonQuantile (Real.toNNReal (rate p.1).get) (p.2.2 0).2.2)).val :=
    measurable_sealDraw.comp (measurable_poissonQuantile.comp
      ((getm (hr.comp measurable_fst)).prodMk
        ((measurable_snd.comp measurable_snd).comp ((measurable_pi_apply 0).comp
          measurable_snd.snd))))
  have h : Measurable fun p : A × ℕ × Tape d =>
      exec (k p.1 (sealDraw (poissonQuantile (Real.toNNReal (rate p.1).get) (p.2.2 0).2.2)).val)
        p.2.1 p.2.2.tail :=
    Measurable.comp hk ((measurable_fst.prodMk hq).prodMk
      (measurable_snd.fst.prodMk (measurable_tape_tail.comp measurable_snd.snd)))
  exact h.fst.prodMk ((measurable_const.add h.snd.fst).prodMk h.snd.snd)

theorem MeasFam.binomT {N : A → Num ℕ} (hN : Measurable N) {k : A → Num ℕ → Tree d β}
    (hk : MeasFam fun p : A × Num ℕ => k p.1 p.2) :
    MeasFam fun a => (Tree.binomT (N a)).bind (k a) := by
  have hq : Measurable fun p : A × ℕ × Tape d =>
      (sealDraw (binomialHalfQuantile (N p.1).get (p.2.2 0).2.2)).val :=
    measurable_sealDraw.comp (measurable_binomialHalfQuantile.comp
      ((Num.measurable_get.comp (hN.comp measurable_fst)).prodMk
        ((measurable_snd.comp measurable_snd).comp ((measurable_pi_apply 0).comp
          measurable_snd.snd))))
  have h : Measurable fun p : A × ℕ × Tape d =>
      exec (k p.1 (sealDraw (binomialHalfQuantile (N p.1).get (p.2.2 0).2.2)).val)
        p.2.1 p.2.2.tail :=
    Measurable.comp hk ((measurable_fst.prodMk hq).prodMk
      (measurable_snd.fst.prodMk (measurable_tape_tail.comp measurable_snd.snd)))
  exact h.fst.prodMk ((measurable_const.add h.snd.fst).prodMk h.snd.snd)

theorem MeasFam.queryCapT (c : Num ℕ) {k : A → Unit → Tree d β}
    (hk : MeasFam fun a => k a ()) : MeasFam fun a => (Tree.queryCapT c).bind (k a) := by
  have h : Measurable fun p : A × ℕ × Tape d => exec (k p.1 ()) c.get p.2.2 :=
    Measurable.comp hk (measurable_fst.prodMk (measurable_const.prodMk measurable_snd.snd))
  exact h.fst.prodMk ((measurable_const.add h.snd.fst).prodMk h.snd.snd)

theorem MeasFam.spendT {k : A → Bool → Tree d β} (hk : MeasFam fun p : A × Bool => k p.1 p.2) :
    MeasFam fun a => Tree.spendT.bind (k a) := by
  have h0 : Measurable fun p : A × ℕ × Tape d => exec (k p.1 false) 0 p.2.2 :=
    Measurable.comp hk ((measurable_fst.prodMk measurable_const).prodMk
      (measurable_const.prodMk measurable_snd.snd))
  have h1 : Measurable fun p : A × ℕ × Tape d => exec (k p.1 true) (p.2.1 - 1) p.2.2 :=
    Measurable.comp hk ((measurable_fst.prodMk measurable_const).prodMk
      ((measurable_snd.fst.sub_const 1).prodMk measurable_snd.snd))
  have heq : (fun p : A × ℕ × Tape d => exec (Tree.spendT.bind (k p.1)) p.2.1 p.2.2) =
      fun p => if p.2.1 ∈ ({0} : Set ℕ) then exec (k p.1 false) 0 p.2.2
        else exec (k p.1 true) (p.2.1 - 1) p.2.2 := by
    funext p
    rcases p with ⟨a, _ | b, t⟩ <;> rfl
  unfold MeasFam
  rw [heq]
  exact Measurable.ite (measurable_snd.fst (measurableSet_singleton 0)) h0 h1

theorem MeasFam.iteB {c : A → Bool} (hc : Measurable c) {f g : A → Tree d β} (hf : MeasFam f)
    (hg : MeasFam g) : MeasFam fun a => if c a then f a else g a := by
  have := MeasFam.ite (P := fun a => c a = true) (hc (measurableSet_singleton true)) hf hg
  exact this

theorem MeasFam.iteP {P : A → Prop} [DecidablePred P] (hP : MeasurableSet {a | P a})
    {f g : A → Tree d β} (hf : MeasFam f) (hg : MeasFam g) :
    MeasFam fun a => if P a then f a else g a :=
  MeasFam.ite hP hf hg

/-- A case split on an optional value. -/
theorem MeasFam.optionMatch [Inhabited β] {o : A → Option β} (ho : Measurable o)
    {f : A → Tree d γ} {g : A → β → Tree d γ} (hf : MeasFam f)
    (hg : MeasFam fun p : A × β => g p.1 p.2) :
    MeasFam fun a => match o a with
      | none => f a
      | some x => g a x := by
  have := (MeasFam.option (f := f) (g := fun p => g p.1 p.2) hf hg).comp
    (φ := fun a => (a, o a)) (measurable_id.prodMk ho)
  refine this.congr fun a => ?_
  rcases o a <;> rfl

/-- A case split on a sum. -/
theorem MeasFam.sumMatch {β' : Type} [MeasurableSpace β'] {s : A → β ⊕ β'} (hs : Measurable s)
    {f : A → β → Tree d γ} {g : A → β' → Tree d γ}
    (hf : MeasFam fun p : A × β => f p.1 p.2) (hg : MeasFam fun p : A × β' => g p.1 p.2) :
    MeasFam fun a => match s a with
      | .inl x => f a x
      | .inr y => g a y := by
  let X := A × ℕ × Tape d
  let H₁ : X × β → Option γ × ℕ × ℕ × Tape d := fun q => exec (f q.1.1 q.2) q.1.2.1 q.1.2.2
  let H₂ : X × β' → Option γ × ℕ × ℕ × Tape d := fun q => exec (g q.1.1 q.2) q.1.2.1 q.1.2.2
  have h₁ : Measurable H₁ := Measurable.comp hf ((measurable_fst.fst.prodMk measurable_snd).prodMk
    measurable_fst.snd)
  have h₂ : Measurable H₂ := Measurable.comp hg ((measurable_fst.fst.prodMk measurable_snd).prodMk
    measurable_fst.snd)
  have hG : Measurable fun q : X × (β ⊕ β') => Sum.elim H₁ H₂ (MeasurableEquiv.prodSumDistrib X β β' q) :=
    (h₁.sumElim h₂).comp (MeasurableEquiv.prodSumDistrib X β β').measurable
  have heq : (fun q : X => exec (match s q.1 with
      | .inl x => f q.1 x
      | .inr y => g q.1 y) q.2.1 q.2.2) =
      (fun q : X × (β ⊕ β') => Sum.elim H₁ H₂ (MeasurableEquiv.prodSumDistrib X β β' q)) ∘
        fun q : X => (q, s q.1) := by
    funext q
    simp only [Function.comp_apply]
    rcases s q.1 with x | y <;> rfl
  unfold MeasFam
  rw [heq]
  exact hG.comp (measurable_id.prodMk (hs.comp measurable_fst))

/-! ## Recovery -/

omit [MeasurableSpace β] in
theorem exec_orElse (p q : Tree d β) (b : ℕ) (t : Tape d) :
    exec (p.orElse q) b t =
      match exec p b t with
      | (some a, m, b', t') => (some a, m, b', t')
      | (none, m, b', t') =>
          let r := exec q b' t'
          (r.1, m + r.2.1, r.2.2) := by
  induction p generalizing b t with
  | pure a => rfl
  | fail => show exec q b t = _; simp [exec]
  | step c k ih =>
      simp only [orElse, exec, ih]
      rcases exec (k c.val) b t with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | coin k ih =>
      simp only [orElse, exec, ih]
      rcases exec (k (t 0).1) b t.tail with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | unit k ih =>
      simp only [orElse, exec, ih]
      rcases exec (k (t 0).2.2) b t.tail with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | gaussian k ih =>
      simp only [orElse, exec, ih]
      rcases exec (k (t 0).2.1) b t.tail with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | poisson r k ih =>
      simp only [orElse, exec, ih]
      rcases exec (k _) b t.tail with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | binom N k ih =>
      simp only [orElse, exec, ih]
      rcases exec (k _) b t.tail with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | setBudget c k ih =>
      simp only [orElse, exec, ih]
      rcases exec k c.get t with ⟨_ | a, m, b', t'⟩ <;> simp [add_assoc]
  | spend k ih =>
      cases b with
      | zero => exact ih false 0 t
      | succ b => exact ih true b t

theorem MeasFam.orElse [Inhabited β] {p q : A → Tree d β} (hp : MeasFam p) (hq : MeasFam q) :
    MeasFam fun a => (p a).orElse (q a) := by
  let Φ : (A × ℕ × ℕ × Tape d) × Option β → Option β × ℕ × ℕ × Tape d := fun z =>
    match z.2 with
    | some a => (some a, z.1.2.1, z.1.2.2.1, z.1.2.2.2)
    | none =>
        let r := exec (q z.1.1) z.1.2.2.1 z.1.2.2.2
        (r.1, z.1.2.1 + r.2.1, r.2.2)
  have hΦ : Measurable Φ := by
    have hr : Measurable fun z : A × ℕ × ℕ × Tape d => exec (q z.1) z.2.2.1 z.2.2.2 :=
      Measurable.comp hq (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk
        measurable_snd.snd.snd))
    have := ArlibCommunity.Algorithms.CV18.Measurable.optionCases (α := β)
      (γ := A × ℕ × ℕ × Tape d) default
      (noneValue := fun z => ((exec (q z.1) z.2.2.1 z.2.2.2).1,
        z.2.1 + (exec (q z.1) z.2.2.1 z.2.2.2).2.1, (exec (q z.1) z.2.2.1 z.2.2.2).2.2))
      (someValue := fun w => (some w.2, w.1.2.1, w.1.2.2.1, w.1.2.2.2))
      (hr.fst.prodMk ((measurable_snd.fst.add hr.snd.fst).prodMk hr.snd.snd))
      ((measurable_some.comp measurable_snd).prodMk (measurable_fst.snd.fst.prodMk
        (measurable_fst.snd.snd.fst.prodMk measurable_fst.snd.snd.snd)))
    convert this using 1
    funext z
    rcases z with ⟨z1, _ | v⟩ <;> rfl
  have hrun : Measurable fun z : A × ℕ × Tape d =>
      ((z.1, (exec (p z.1) z.2.1 z.2.2).2), (exec (p z.1) z.2.1 z.2.2).1) :=
    (measurable_fst.prodMk hp.snd).prodMk hp.fst
  have heq : (fun z : A × ℕ × Tape d => exec ((p z.1).orElse (q z.1)) z.2.1 z.2.2) =
      Φ ∘ fun z => ((z.1, (exec (p z.1) z.2.1 z.2.2).2), (exec (p z.1) z.2.1 z.2.2).1) := by
    funext z
    rw [exec_orElse]
    simp only [Function.comp_apply, Φ]
    rcases exec (p z.1) z.2.1 z.2.2 with ⟨_ | x, m, b', t'⟩ <;> rfl
  unfold MeasFam
  rw [heq]
  exact hΦ.comp hrun

/-! ## Loops -/

instance sumInhabitedLeft {β β' : Type} [Inhabited β] : Inhabited (β ⊕ β') := ⟨Sum.inl default⟩


theorem MeasFam.loopRounds [Inhabited β] {β' : Type} [MeasurableSpace β']
    {body : A → β → Tree d (β ⊕ β')} (hbody : MeasFam fun p : A × β => body p.1 p.2) :
    ∀ k : ℕ, MeasFam fun p : A × β => ttc.Tape.loopRounds (body p.1) k p.2
  | 0 => MeasFam.pure (measurable_inl.comp measurable_snd)
  | k + 1 => by
      have key := MeasFam.bind' (k := fun (p : A × β) (r : β ⊕ β') => match r with
          | .inl b' => ttc.Tape.loopRounds (body p.1) k b'
          | .inr c => Tree.pure (Sum.inr c)) hbody
        (MeasFam.sumMatch (s := fun q : (A × β) × (β ⊕ β') => q.2) measurable_snd
          (f := fun q b' => ttc.Tape.loopRounds (body q.1.1) k b')
          (g := fun q c => Tree.pure (Sum.inr c))
          ((MeasFam.loopRounds hbody k).comp (measurable_fst.fst.fst.prodMk measurable_snd))
          (MeasFam.pure (measurable_inr.comp measurable_snd)))
      refine key.congr fun p => ?_
      show _ = (body p.1 p.2).bind _
      rfl

theorem MeasFam.loopTree [Inhabited β] {β' : Type} [MeasurableSpace β']
    {count : A → Num ℕ} (hcount : Measurable count) {body : A → β → Tree d (β ⊕ β')}
    (hbody : MeasFam fun p : A × β => body p.1 p.2) {init : A → β} (hinit : Measurable init) :
    MeasFam fun a => ttc.Tape.loopTree (count a) (body a) (init a) := by
  unfold MeasFam
  refine measurable_of_nat_cases (K := fun z : A × ℕ × Tape d => (count z.1).get)
    (Num.measurable_get.comp (hcount.comp measurable_fst))
    (G := fun k z => exec (ttc.Tape.loopTree (count z.1) (body z.1) (init z.1)) z.2.1 z.2.2 |> fun _ =>
      exec (Tree.step (Charged.op (Op.num .loop) () : Prog Unit) fun _ =>
        ttc.Tape.loopRounds (body z.1) k (init z.1)) z.2.1 z.2.2) (fun k => ?_) fun z => rfl
  have h := (MeasFam.stepConst (A := A) (Charged.op (Op.num .loop) () : Prog Unit)
    (k := fun a _ => ttc.Tape.loopRounds (body a) k (init a))
    ((MeasFam.loopRounds hbody k).comp (measurable_id.prodMk hinit)))
  exact h

/-! ## Folds -/

theorem MeasFam.foldlM_fixed {α : Type} {g : A → β → α → Tree d β}
    [Inhabited β] (hg : ∀ x, MeasFam fun p : A × β => g p.1 p.2 x) :
    ∀ (l : List α), MeasFam fun p : A × β => l.foldlM (g p.1) p.2
  | [] => MeasFam.pure measurable_snd
  | x :: l => by
      have key := MeasFam.bind' (k := fun (p : A × β) acc => l.foldlM (g p.1) acc) (hg x)
        ((MeasFam.foldlM_fixed hg l).comp (measurable_fst.fst.prodMk measurable_snd))
      refine key.congr fun p => ?_
      rfl

theorem MeasFam.foldlM_ofFn {α : Type} [MeasurableSpace α] [Inhabited β]
    {g : A → β → α → Tree d β} (hg : MeasFam fun p : A × β × α => g p.1 p.2.1 p.2.2) :
    ∀ k : ℕ, MeasFam fun p : A × β × (Fin k → α) => (List.ofFn p.2.2).foldlM (g p.1) p.2.1
  | 0 => (MeasFam.pure measurable_snd.fst).congr fun p => by simp
  | k + 1 => by
      have key := MeasFam.bind'
        (k := fun (p : A × β × (Fin (k + 1) → α)) acc =>
          (List.ofFn (Fin.tail p.2.2)).foldlM (g p.1) acc)
        (hg.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
          ((measurable_pi_apply 0).comp measurable_snd.snd))))
        ((MeasFam.foldlM_ofFn hg k).comp (measurable_fst.fst.prodMk (measurable_snd.prodMk
          (measurable_fin_tail.comp measurable_fst.snd.snd))))
      refine key.congr fun p => ?_
      rw [List.ofFn_succ (f := p.2.2)]
      rfl

/-- A family of trees on lists runs measurably when it does on the lists of each length. -/
theorem MeasFam.ofList {α : Type} [MeasurableSpace α] [Inhabited α] {F : A → List α → Tree d β}
    (h : ∀ k, MeasFam fun p : A × (Fin k → α) => F p.1 (List.ofFn p.2)) :
    MeasFam fun p : A × List α => F p.1 p.2 := by
  have hX : Measurable fun z : (A × ℕ × Tape d) × List α => exec (F z.1.1 z.2) z.1.2.1 z.1.2.2 :=
    measurable_of_ofFn fun k => Measurable.comp (h k)
      ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  exact hX.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

theorem MeasFam.foldlM {α : Type} [MeasurableSpace α] [Inhabited α] [Inhabited β]
    {g : A → β → α → Tree d β} (hg : MeasFam fun p : A × β × α => g p.1 p.2.1 p.2.2)
    {L : A → List α} (hL : Measurable L) {init : A → β} (hinit : Measurable init) :
    MeasFam fun a => (L a).foldlM (g a) (init a) := by
  have h := MeasFam.ofList (A := A × β) (F := fun p l => l.foldlM (g p.1) p.2)
    fun k => (MeasFam.foldlM_ofFn hg k).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact h.comp ((measurable_id.prodMk hinit).prodMk hL)

end Tree

/-! ## The state of the algorithm -/

instance State.instMeasurableSpace (d : ℕ) : MeasurableSpace (State d) :=
  MeasurableSpace.comap (fun s : State d => (s.p, s.X, s.size)) inferInstance

instance State.instInhabited (d : ℕ) : Inhabited (State d) := ⟨⟨default, [], default⟩⟩

theorem State.measurable_p {d : ℕ} : Measurable (State.p : State d → Num ℝ) :=
  measurable_fst.comp (comap_measurable _)

theorem State.measurable_X {d : ℕ} : Measurable (State.X : State d → List (Fin d → Num ℤ)) :=
  measurable_snd.fst.comp (comap_measurable _)

theorem State.measurable_size {d : ℕ} : Measurable (State.size : State d → Num ℕ) :=
  measurable_snd.snd.comp (comap_measurable _)

theorem State.measurable_mk {d : ℕ} {Q : Type} [MeasurableSpace Q] {p : Q → Num ℝ}
    {X : Q → List (Fin d → Num ℤ)} {size : Q → Num ℕ} (hp : Measurable p) (hX : Measurable X)
    (hs : Measurable size) : Measurable fun q => (⟨p q, X q, size q⟩ : State d) := by
  intro S hS
  obtain ⟨T, hT, rfl⟩ := hS
  exact (hp.prodMk (hX.prodMk hs)) hT

theorem measurable_sum_empty {β : Type} [MeasurableSpace β] :
    Measurable fun s : β ⊕ Empty => match s with
      | .inl y => y
      | .inr e => e.elim := by
  have : (fun s : β ⊕ Empty => match s with
      | .inl y => y
      | .inr e => e.elim) = Sum.elim id Empty.elim := by
    funext s; rcases s with y | e <;> rfl
  rw [this]
  exact measurable_id.sumElim (measurable_from_top)

end ttc.Tape
