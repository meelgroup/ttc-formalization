/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.StepAssembly

/-!
# The loop over the components

The sealed program runs the step on each component in turn.  The step sets CV18's query cap
before spending from it (`CapFirst`), so its result does not depend on the cap it starts
with, and the steps compose (`vlaw_bind_capFirst`).  Read through the state views, the loop
has the law of the old loop with the same fuel (`oldFoldF`, `fold_piece`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc (TTCState)
open ArlibCommunity.Algorithms.CV18 (measurable_some)

variable {d : ℕ}

/-! ## Trees that set the cap before spending from it -/

section CapFirst

variable {α β γ : Type}

/-- **No call is spent before the cap is set.** -/
def CapFirst : Tree d α → Prop
  | .pure _ => True
  | .fail => True
  | .step c k => CapFirst (k c.val)
  | .coin k => ∀ x, CapFirst (k x)
  | .unit k => ∀ x, CapFirst (k x)
  | .gaussian k => ∀ x, CapFirst (k x)
  | .poisson _ k => ∀ x, CapFirst (k x)
  | .binom _ k => ∀ x, CapFirst (k x)
  | .setBudget _ _ => True
  | .spend _ => False

theorem CapFirst.bind {p : Tree d α} {f : α → Tree d β} (hp : CapFirst p)
    (hf : ∀ a, CapFirst (f a)) : CapFirst (p.bind f) := by
  induction p with
  | pure a => exact hf a
  | fail => trivial
  | step c k ih => exact ih c.val hp
  | coin k ih => exact fun x => ih x (hp x)
  | unit k ih => exact fun x => ih x (hp x)
  | gaussian k ih => exact fun x => ih x (hp x)
  | poisson r k ih => exact fun x => ih x (hp x)
  | binom N k ih => exact fun x => ih x (hp x)
  | setBudget c k ih => trivial
  | spend k ih => exact hp.elim

theorem Free.capFirst {p : Tree d α} (hp : Free p) : CapFirst p := by
  induction p with
  | pure a => trivial
  | fail => trivial
  | step c k ih => exact ih c.val hp
  | coin k ih => exact fun x => ih x (hp x)
  | unit k ih => exact fun x => ih x (hp x)
  | gaussian k ih => exact fun x => ih x (hp x)
  | poisson r k ih => exact fun x => ih x (hp x)
  | binom N k ih => exact fun x => ih x (hp x)
  | setBudget c k ih => exact hp.elim
  | spend k ih => exact hp.elim

theorem capFirst_compute (c : Prog α) : CapFirst (compute (n := d) c) := trivial

theorem capFirst_foldlM {ι : Type} {g : β → ι → Tree d β} (hg : ∀ b x, CapFirst (g b x)) :
    ∀ (l : List ι) (b : β), CapFirst (l.foldlM g b)
  | [], _ => trivial
  | x :: l, b => by
      simp only [List.foldlM_cons]
      exact CapFirst.bind (hg b x) fun b' => capFirst_foldlM hg l b'

theorem capFirst_loopRounds {body : β → Tree d (β ⊕ γ)} (hb : ∀ y, CapFirst (body y)) :
    ∀ (k : ℕ) (y : β), CapFirst (loopRounds body k y)
  | 0, _ => trivial
  | k + 1, y => CapFirst.bind (hb y) fun r => by
      rcases r with y' | c
      · exact capFirst_loopRounds hb k y'
      · trivial

/-- A tree that sets the cap first gives the same result whatever cap it starts with. -/
theorem exec_fst_of_capFirst {p : Tree d α} (hp : CapFirst p) (b b' : ℕ) (t : Tape d) :
    (exec p b t).1 = (exec p b' t).1 := by
  induction p generalizing t with
  | pure a => rfl
  | fail => rfl
  | step c k ih => exact ih c.val hp t
  | coin k ih => exact ih _ (hp _) _
  | unit k ih => exact ih _ (hp _) _
  | gaussian k ih => exact ih _ (hp _) _
  | poisson r k ih => exact ih _ (hp _) _
  | binom N k ih => exact ih _ (hp _) _
  | setBudget c k ih => rfl
  | spend k ih => exact hp.elim

variable [MeasurableSpace α] [MeasurableSpace β]

theorem vlaw_eq_of_capFirst {p : Tree d α} (hp : CapFirst p)
    (hm : ∀ c, Measurable fun t => outcome (exec p c t)) (b b' : ℕ) : vlaw p b = vlaw p b' := by
  rw [vlaw, vlaw, ← tapeLaw_map_exec p b (hm b), ← tapeLaw_map_exec p b' (hm b'),
    Measure.map_map measurable_fst (hm b), Measure.map_map measurable_fst (hm b')]
  congr 1
  funext t
  exact exec_fst_of_capFirst hp b b' t

/-- **A sequence whose continuation sets the cap first**, at any cap for the continuation. -/
theorem vlaw_bind_capFirst {f : α → Tree d β} (hf : MeasFam f) (hcf : ∀ a, CapFirst (f a))
    (p : Tree d α) (b : ℕ) (hp : Measurable fun t => outcome (exec p b t)) (c : ℕ) :
    vlaw (p.bind f) b = (vlaw p b).bind fun o => o.elim (Measure.dirac none) fun a => vlaw (f a) c := by
  have hK := measurable_optionKernel (hf.measurable_vlaw c)
  rw [vlaw, law_bind hf p b hp, Measure.map_bind (measurable_cont hf).aemeasurable
    measurable_fst.aemeasurable, vlaw, Measure.bind_map measurable_fst.aemeasurable hK.aemeasurable]
  congr 1
  funext o
  obtain ⟨_ | a, m, b'⟩ := o
  · simp only [cont, Option.elim]
    rw [Measure.map_dirac' measurable_fst]
  · simp only [cont, Option.elim]
    rw [Measure.map_map measurable_fst (measurable_addOps m)]
    exact vlaw_eq_of_capFirst (hcf a) (fun c' => hf.outcome a c') b' c

end CapFirst

section StepCap

theorem capFirst_cv18T (member : NumPoint d → Prog Bool) (eps r p : Num ℝ) :
    CapFirst (cv18T d member eps r p) := by
  unfold cv18T repeatIndependentlyT loopTree
  refine CapFirst.bind trivial fun G => CapFirst.bind (CapFirst.bind ?_ fun _ => trivial)
    fun _ => trivial
  refine capFirst_loopRounds (fun est => CapFirst.bind ?_ fun x => ?_) _ _
  · trivial
  · exact CapFirst.bind trivial fun _ => trivial

theorem capFirst_stepT (fuel : ℕ) (K : Params) (L : Loaded d) (s : State d) :
    CapFirst (stepT (cv18T d) fuel K L s) := by
  rw [stepT_eq]
  refine CapFirst.bind trivial fun _ => CapFirst.bind trivial fun x => ?_
  refine CapFirst.bind (capFirst_cv18T _ _ _ _) fun v => ?_
  refine Free.capFirst ?_
  exact Free.bind (free_compute _) fun t => Free.bind (free_compute _) fun sc =>
    Free.bind (free_rateT _ _ _ _ _) fun q => free_tailT _ _ _ _ _ _

end StepCap

/-! ## The old loop with fuel: what its states look like -/

section OldInv

variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

/-- **What holds for every result of every kernel step holds after the bind.** -/
theorem ae_bind_of_ae {μ : Measure α} {K : α → Measure β} (hK : AEMeasurable K μ) {P : α → Prop}
    {Q : β → Prop} (hQ : MeasurableSet {x | Q x}) (hP : ∀ᵐ a ∂μ, P a)
    (h : ∀ a, P a → ∀ᵐ x ∂K a, Q x) : ∀ᵐ x ∂μ.bind K, Q x := by
  rw [ae_iff, show {x | ¬Q x} = {x | Q x}ᶜ from rfl, Measure.bind_apply hQ.compl hK]
  have : (fun a => K a {x | Q x}ᶜ) =ᵐ[μ] 0 := hP.mono fun a ha => by
    have := h a ha
    rw [ae_iff] at this
    exact this
  rw [lintegral_congr_ae this]
  simp

/-- The old invariant at precision `b`, with `p` a dyadic fraction of `c`. -/
def DyInv (b : ℕ) (c : NNReal) (s : TTCState d) : Prop := StInv b s ∧ ∃ j : ℕ, s.p = c / 2 ^ j

theorem measurable_stateP : Measurable fun s : TTCState d => s.p :=
  measurable_fst.comp (comap_measurable fun s : TTCState d => (s.p, s.X, s.nextLabel))

theorem measurableSet_dyInv (b : ℕ) (c : NNReal) : MeasurableSet {s : TTCState d | DyInv b c s} := by
  have : {s : TTCState d | DyInv b c s} =
      {s | StInv b s} ∩ ⋃ j : ℕ, (fun s : TTCState d => s.p) ⁻¹' {c / 2 ^ j} := by
    ext s
    simp [DyInv]
  rw [this]
  exact (measurableSet_stInv b).inter
    (MeasurableSet.iUnion fun j => measurable_stateP (measurableSet_singleton _))

theorem countable_dyadic (c : NNReal) :
    {o : Option (TTCState d) | ∀ s ∈ o, ∃ j : ℕ, s.p = c / 2 ^ j}.Countable := by
  refine (countable_range (fun o : Option (ℕ × Finset (ttc.SampleCopy d) × ℕ) =>
    o.map fun w => (⟨c / 2 ^ w.1, w.2.1, w.2.2⟩ : TTCState d))).mono ?_
  rintro (_ | s) hs
  · exact ⟨none, rfl⟩
  · obtain ⟨j, hj⟩ := hs s rfl
    refine ⟨some (j, s.X, s.nextLabel), ?_⟩
    show some (⟨c / 2 ^ j, s.X, s.nextLabel⟩ : TTCState d) = some s
    rw [← hj]

/-- **The old loop's laws are almost everywhere measurable kernels' domains**: they live on
states whose `p` is a dyadic fraction of a fixed number. -/
theorem aemeasurable_of_dyadic {μ : Measure (Option (TTCState d))} {c : NNReal}
    (h : ∀ᵐ o ∂μ, ∀ s ∈ o, ∃ j : ℕ, s.p = c / 2 ^ j) (f : Option (TTCState d) → β) :
    AEMeasurable f μ :=
  aemeasurable_of_countable_support (countable_dyadic c) (ae_iff.mp h) f

theorem addList_stInv (b : ℕ) (s : TTCState d) (zs : List (Fin d → ℤ)) (hs : StInv b s) :
    StInv b (addList b s zs) := by
  classical
  refine ⟨s.labelsFresh_addBatch _ hs.1, fun c hc => ?_⟩
  simp only [addList, ttc.TTCState.addBatch, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hc
  rcases hc with hc | ⟨i, rfl⟩
  · exact hs.2 c hc
  · rfl

theorem sampleKernel_inv (ν : Measure (Option (Fin d → ℤ))) (b : ℕ) (c : NNReal)
    (sec : TTCState d × ℕ) (hs : DyInv b c sec.1) :
    ∀ᵐ o ∂sampleKernel ν b sec, ∀ s ∈ o, DyInv b c s := by
  rw [sampleKernel, ae_map_iff (measurable_of_countable _).aemeasurable
    (measurableSet_forall_mem (measurableSet_dyInv b c))]
  refine ae_of_all _ fun o s hs' => ?_
  rcases o with _ | zs
  · cases hs'
  · cases hs'
    exact ⟨addList_stInv b sec.1 zs hs.1, hs.2⟩

theorem oldLaw_dyInv (Th : ℝ) (f : ℕ) (s : TTCState d) (N b : ℕ) (c : NNReal) (hs : DyInv b c s) :
    ∀ᵐ o ∂oldLaw Th f s N, ∀ a ∈ o, DyInv b c a.1 := by
  classical
  have hm : MeasurableSet {a : TTCState d × ℕ | DyInv b c a.1} :=
    measurable_fst (measurableSet_dyInv b c)
  rw [oldLaw, ae_map_iff (measurable_oldTrunc Th f s N).aemeasurable (measurableSet_forall_mem hm)]
  refine ae_of_all _ fun coins a ha => ?_
  simp only [oldTrunc] at ha
  split_ifs at ha
  swap
  · cases ha
  cases ha
  obtain ⟨j, hj⟩ := hs.2
  refine ⟨⟨ttc.thinningResult_labelsFresh s N Th coins hs.1.1, fun c' hc' => hs.1.2 c' ?_⟩, ?_⟩
  · exact (Finset.mem_filter.mp hc').1
  · refine ⟨j + ttcPseudocode.secondLoopExitRound s N Th coins, ?_⟩
    show s.p / 2 ^ _ = _
    rw [hj, pow_add, div_div]

theorem oldTail_dyInv (Th : ℝ) (fuel : ℕ) (ν : Measure (Option (Fin d → ℤ))) (b : ℕ) (t : NNReal)
    (c : NNReal) (y : TTCState d) (hy : DyInv b c y) :
    ∀ᵐ o ∂oldTail Th fuel ν b t y, ∀ s ∈ o, DyInv b c s := by
  have hQ := measurableSet_forall_mem (measurableSet_dyInv (d := d) b c)
  refine ae_bind_of_ae (P := fun _ => True) (measurable_of_countable _).aemeasurable hQ
    (ae_of_all _ fun _ => trivial) fun N _ => ?_
  refine ae_bind_of_ae (aemeasurable_oldLaw Th fuel y N _) hQ
    (oldLaw_dyInv Th fuel y N b c hy) fun o ho => ?_
  rcases o with _ | sec
  · exact (ae_dirac_iff hQ).mpr fun a ha => by cases ha
  · exact sampleKernel_inv ν b c sec (ho sec rfl)

theorem rateCheck_dyInv (P : ttc.PolytopeData d) (Th : ℝ) (b : ℕ) (y : TTCState d) (t : NNReal)
    (hy : StInv b y) :
    ∀ᵐ y1 ∂ttcPseudocode.rateCheck (y.removeComponent P) t Th, DyInv b y.p y1 := by
  classical
  rw [ttcPseudocode.rateCheck, ae_map_iff (measurable_rateCheckResult _ t Th).aemeasurable
    (measurableSet_dyInv b y.p)]
  refine ae_of_all _ fun coins => ?_
  have hfresh := (y.removeComponent P).labelsFresh_samplesAfter coins
    (ttcPseudocode.rateHalvings (y.removeComponent P) t Th)
    ((y.labelsFresh_removeComponent P) hy.1)
  refine ⟨⟨hfresh, fun c' hc' => hy.2 c' ?_⟩, ⟨ttcPseudocode.rateHalvings _ t Th, rfl⟩⟩
  have h1 := (Finset.mem_filter.mp hc').1
  exact (Finset.mem_filter.mp h1).1

/-- **After an old step with fuel, the states keep the invariant and a dyadic `p`.** -/
theorem oldStepF_dyInv (hn : 3 ≤ d) (P : ttc.PolytopeData d) (Th : ℝ) (fuel : ℕ)
    (ν : Measure (Option (Fin d → ℤ))) (b : ℕ) (eta delta : ℝ) (y : TTCState d)
    (hy : StInv b y) :
    ∀ᵐ o ∂oldStepF P Th fuel ν b hn eta delta y, ∀ s ∈ o, DyInv b y.p s := by
  have hQ := measurableSet_forall_mem (measurableSet_dyInv (d := d) b y.p)
  refine ae_bind_of_ae (P := fun _ => True) (measurable_gvF_vol P Th fuel ν b y).aemeasurable hQ
    (ae_of_all _ fun _ => trivial) fun vol _ => ?_
  exact ae_bind_of_ae (aemeasurable_rateCheck Th _ _ _) hQ (rateCheck_dyInv P Th b y _ hy)
    fun y1 hy1 => oldTail_dyInv Th fuel ν b _ y.p y1 hy1

end OldInv

/-! ## What every sealed step gives -/

section NewInv

theorem post_sampleT (fuel : ℕ) (K : Params) (L : Loaded d) (scaled : Fin L.facets → Num ℝ)
    (h : Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ) (hs : h.2.2.1.get = h.2.1.length)
    (hp : 0 ≤ h.1.get) :
    Post (sampleT fuel K L scaled h) fun s => 0 ≤ s.p.get ∧ s.size.get = s.X.length := by
  unfold sampleT
  refine post_compute_bind ?_
  show Post ((loopRounds _ h.2.2.2.get (h.2.1, h.2.2.1)).bind _) _
  refine Post.bind ((post_loopRounds (I := fun acc : List (Fin d → Num ℤ) × Num ℕ =>
    acc.2.get = acc.1.length) (R := fun _ : Empty => False) (fun acc hacc => ?_) _ _ hs).mono
      fun r hr => ?_)
  · unfold sampleBody
    refine Post.bind (post_of_forall (fun z => ?_) _)
    refine post_compute_bind (post_compute_bind ?_)
    show (A.add acc.2 _).val.get = (A.push acc.1 z).val.length
    simp [A.push, ttc.Model.Operations.push, A.add, A.lit, Num.get_add, hacc]
    rfl
  · rcases r with acc | e
    · exact ⟨hp, hr⟩
    · exact e.elim

theorem post_tailT (fuel : ℕ) (K : Params) (L : Loaded d) (t : Num ℝ)
    (scaled : Fin L.facets → Num ℝ) (q : Num ℝ × List (Fin d → Num ℤ) × Num ℕ)
    (hq : 0 ≤ q.1.get) (hs : q.2.2.get = q.2.1.length) :
    Post (tailT fuel K L t scaled q) fun s => 0 ≤ s.p.get ∧ s.size.get = s.X.length := by
  rw [tailT_eq]
  refine post_compute_bind (Post.bind (post_of_forall (fun N => ?_) _))
  exact Post.bind ((post_halveT K fuel q.1 q.2.1 q.2.2 N hs hq).mono fun h hh =>
    post_sampleT fuel K L scaled h hh.1 hh.2)

/-- **A sealed step keeps `p ≥ 0` and the count equal to the list's length.** -/
theorem post_stepT (fuel : ℕ) (K : Params) (L : Loaded d) (s : State d) (hp : 0 ≤ s.p.get) :
    Post (stepT (cv18T d) fuel K L s) fun s' => 0 ≤ s'.p.get ∧ s'.size.get = s'.X.length := by
  rw [stepT_eq]
  refine post_compute_bind (post_compute_bind (Post.bind (post_of_forall (fun v => ?_) _)))
  refine post_compute_bind (post_compute_bind ?_)
  exact Post.bind ((post_rateT _ _ _ _ s hp).mono fun q hq => post_tailT _ _ _ _ _ q hq.1 hq.2)

theorem measurableSet_stateOk :
    MeasurableSet {s : State d | 0 ≤ s.p.get ∧ s.size.get = s.X.length} :=
  (measurableSet_Ici.preimage (Num.measurable_get.comp State.measurable_p)).inter
    (measurableSet_eq_fun (Num.measurable_get.comp State.measurable_size)
      (List.measurable_length.comp State.measurable_X))

end NewInv

/-! ## The loop -/

section Fold

variable (hn : 3 ≤ d) (eta delta Th : ℝ) (fuel b : ℕ)
  (ν : ttc.PolytopeData d → Measure (Option (Fin d → ℤ)))

/-- **The old loop over the components with fuel.** -/
def oldFoldF : List (ttc.PolytopeData d) → TTCState d → Measure (Option (TTCState d))
  | [], y => Measure.dirac (some y)
  | P :: rest, y => (oldStepF P Th fuel (ν P) b hn eta delta y).bind fun o =>
      o.elim (Measure.dirac none) (oldFoldF rest)

variable (K : Params) (b' : ℕ) (hadm : ttc.CommunityCV18.AdmissibleCV18Request eta delta)
  (he : K.epsPrime.get = eta) (hdl : K.deltaPrime.get = delta) (hth : K.thresh.get = Th)
  (hTh : 0 < Th) (hdim : K.dim.get = d) (hdimN : K.dimN.get = d)
  (hs : K.scale.get = ttc.decimalScale b) (hsN : K.scaleN.get = 10 ^ (b * d))
  (hprob : ∀ P, IsProbabilityMeasure (ν P))

include hadm he hdl hth hTh hdim hdimN hs hsN hprob in
/-- **The sealed loop has the old loop's law with the same fuel**, read through the state
views. -/
theorem fold_piece : ∀ (Ps : List (ttc.PolytopeData d)),
    (∀ P ∈ Ps, (vlaw (sampleUntilAcceptedT (loaded P) (walkConstantsProg (loaded P) K.scale
      K.epsPrime K.dim).val (scaledOffsets (loaded P) K.scale).val K.dimN fuel) b').map
        (Option.map getZ) = ν P) →
    ∀ (x : State d) (y : TTCState d), (stCorr b).Rel x y →
      (vlaw ((Ps.map loaded).foldlM (fun s L => stepT (cv18T d) fuel K L s) x) b').map
          (Option.map stVN) =
        (oldFoldF hn eta delta Th fuel b ν Ps y).map (Option.map stVO)
  | [], _, x, y, hrel => by
      have hvN : Measurable (stVN (d := d)) := (stCorr (d := d) 0).measurable_vN
      have hvO : Measurable (stVO (d := d)) := (stCorr (d := d) 0).measurable_vO
      show (vlaw (Tree.pure x) b').map _ = (Measure.dirac (some y)).map _
      rw [vlaw_pure, Measure.map_dirac' (measurable_optionMap hvN),
        Measure.map_dirac' (measurable_optionMap hvO)]
      simp only [Option.map_some]
      rw [show stVN x = stVO y from hrel.2.2]
  | P :: rest, hν, x, y, hrel => by
      have hvN : Measurable (stVN (d := d)) := (stCorr (d := d) 0).measurable_vN
      have hvO : Measurable (stVO (d := d)) := (stCorr (d := d) 0).measurable_vO
      have := hprob P
      have hmF : MeasFam fun x' : State d =>
          (rest.map loaded).foldlM (fun s L => stepT (cv18T d) fuel K L s) x' :=
        (MeasFam.foldlM_fixed (A := Unit) (g := fun _ s L => stepT (cv18T d) fuel K L s)
          (fun L => mf_step fuel K L measurable_snd) (rest.map loaded)).comp
          (φ := fun x' => ((), x')) (measurable_const.prodMk measurable_id)
      have hcf : ∀ x', CapFirst ((rest.map loaded).foldlM
          (fun s L => stepT (cv18T d) fuel K L s) x') :=
        capFirst_foldlM (fun s L => capFirst_stepT fuel K L s) _
      have hmS : Measurable fun τ => outcome (exec (stepT (cv18T d) fuel K (loaded P) x) b' τ) :=
        (mf_step (Q := Unit) fuel K (loaded P) (s := fun _ => x) measurable_const).outcome () b'
      rw [List.map_cons, List.foldlM_cons]
      change (vlaw ((stepT (cv18T d) fuel K (loaded P) x).bind fun x' =>
        (rest.map loaded).foldlM (fun s L => stepT (cv18T d) fuel K L s) x') b').map _ = _
      rw [vlaw_bind_capFirst hmF hcf _ b' hmS b',
        Measure.map_bind (measurable_optionKernel (hmF.measurable_vlaw b')).aemeasurable
          (measurable_optionMap hvN).aemeasurable]
      have hdy := oldStepF_dyInv hn P Th fuel (ν P) b eta delta y hrel.2.1
      rw [oldFoldF, Measure.map_bind (aemeasurable_of_dyadic (hdy.mono fun o ho s hs => (ho s hs).2) _)
        (measurable_optionMap hvO).aemeasurable]
      refine (stCorr (d := d) b).option.bind_eq
        (step_piece hn P K fuel b b' eta delta Th hadm he hdl hth hTh hdim hdimN hs hsN (ν P)
          (hν P List.mem_cons_self) x y hrel) ?_ (hdy.mono fun o ho s hs => (ho s hs).1) ?_ ?_
      · exact (ae_vlaw_post (post_stepT fuel K (loaded P) x hrel.1) measurableSet_stateOk b'
          hmS).mono fun o ho s hs => (ho s hs).1
      · exact (Measure.measurable_map _ (measurable_optionMap hvN)).comp
          (measurable_optionKernel (hmF.measurable_vlaw b'))
      · rintro (_ | x') (_ | y') ⟨hx', hy', hv⟩
        · show (Measure.dirac (none : Option (State d))).map (Option.map stVN) =
            (Measure.dirac (none : Option (TTCState d))).map (Option.map stVO)
          rw [Measure.map_dirac' (measurable_optionMap hvN),
            Measure.map_dirac' (measurable_optionMap hvO)]
          rfl
        · cases hv
        · cases hv
        · exact fold_piece rest (fun Q hQ => hν Q (List.mem_cons_of_mem P hQ)) x' y'
            ⟨hx' x' rfl, hy' y' rfl, Option.some.inj hv⟩

end Fold

end ttc.Tape
