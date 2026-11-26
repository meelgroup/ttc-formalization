/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.StepTail

/-!
# One step, assembled

The step of the sealed program is CV18 on the component, the scaled volume `t`, the deletion
pass and rate check, and the tail (`stepT_eq`).  Read through the state views it has the law
of the old step with the same fuel (`oldStepF`, `step_piece`).

The old step's kernels are almost everywhere measurable because the old laws they are
integrated against live on countably many states (`aemeasurable_of_countable_support`);
only the dependence on the real volume estimate needs a measurability proof
(`measurable_gvF`).
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

variable {d : ℕ}

/-! ## Laws on countably many points -/

section Countable

variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- **Every function is almost everywhere measurable for a law on countably many points.** -/
theorem aemeasurable_of_countable_support [MeasurableSingletonClass α] {μ : Measure α} {S : Set α}
    (hS : S.Countable) (h : μ Sᶜ = 0) (f : α → β) : AEMeasurable f μ := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact (measurable_of_empty f).aemeasurable
  obtain ⟨a0⟩ := hα
  let g : α → β := fun x => if x ∈ S then f x else f a0
  have hg : Measurable g := by
    intro B hB
    have : g ⁻¹' B = (S ∩ f ⁻¹' B) ∪ (Sᶜ ∩ {_x | f a0 ∈ B}) := by
      ext x
      by_cases hx : x ∈ S <;> simp [g, hx]
    rw [this]
    exact (hS.mono inter_subset_left).measurableSet.union
      (hS.measurableSet.compl.inter (MeasurableSet.const _))
  refine ⟨g, hg, ?_⟩
  refine measure_mono_null (fun x hx => ?_) h
  by_contra hxS
  exact hx (by simp [g, not_not.mp hxS])

theorem aemeasurable_map_of_countable_range [MeasurableSingletonClass α] {μ : Measure γ}
    {g : γ → α} (hg : Measurable g) (hr : (range g).Countable) (f : α → β) :
    AEMeasurable f (μ.map g) :=
  aemeasurable_of_countable_support hr (by
    rw [Measure.map_apply hg hr.measurableSet.compl]
    simp) f

end Countable

/-! ## The old step with fuel -/

section OldStep

variable (P : ttc.PolytopeData d) (Th : ℝ) (fuel : ℕ) (ν : Measure (Option (Fin d → ℤ))) (b : ℕ)

theorem measurable_mkState {Q : Type} [MeasurableSpace Q] {p : Q → NNReal}
    {X : Q → Finset (ttc.SampleCopy d)} {nl : Q → ℕ} (hp : Measurable p) (hX : Measurable X)
    (hnl : Measurable nl) : Measurable fun q => (⟨p q, X q, nl q⟩ : TTCState d) := by
  rw [measurable_comap_iff]
  exact hp.prodMk (hX.prodMk hnl)

theorem countable_range_rateCheckResult (s : TTCState d) (t : NNReal) :
    (range (ttcPseudocode.rateCheckResult s t Th)).Countable := by
  have : range (ttcPseudocode.rateCheckResult s t Th) ⊆
      range (fun X : Finset (ttc.SampleCopy d) =>
        (⟨s.p / 2 ^ ttcPseudocode.rateHalvings s t Th, X, s.nextLabel⟩ : TTCState d)) := by
    rintro _ ⟨c, rfl⟩
    exact ⟨_, rfl⟩
  exact (countable_range _).mono this

theorem countable_range_oldTrunc (f : ℕ) (s : TTCState d) (N : ℕ) :
    (range (oldTrunc Th f s N)).Countable := by
  have : range (oldTrunc Th f s N) ⊆
      range (fun o : Option (ℕ × Finset (ttc.SampleCopy d) × ℕ) =>
        o.map fun w => ((⟨s.p / 2 ^ w.1, w.2.1, s.nextLabel⟩ : TTCState d), w.2.2)) := by
    rintro _ ⟨c, rfl⟩
    unfold oldTrunc
    split_ifs
    · exact ⟨some (ttcPseudocode.secondLoopExitRound s N Th c,
        samplesAfter c (ttcPseudocode.secondLoopExitRound s N Th c) s.X,
        pendingAfter c (ttcPseudocode.secondLoopExitRound s N Th c) s.nextLabel N), rfl⟩
    · exact ⟨none, rfl⟩
  exact (countable_range _).mono this

theorem aemeasurable_oldLaw (f : ℕ) (s : TTCState d) (N : ℕ) {β : Type} [MeasurableSpace β]
    (g : Option (TTCState d × ℕ) → β) : AEMeasurable g (oldLaw Th f s N) :=
  aemeasurable_map_of_countable_range (measurable_oldTrunc Th f s N)
    (countable_range_oldTrunc Th f s N) g

theorem aemeasurable_rateCheck (s : TTCState d) (t : NNReal) {β : Type} [MeasurableSpace β]
    (g : TTCState d → β) : AEMeasurable g (ttcPseudocode.rateCheck s t Th) :=
  aemeasurable_map_of_countable_range (measurable_rateCheckResult s t Th)
    (countable_range_rateCheckResult Th s t) g

/-- The old step after the volume estimate, with fuel: deletion, the rate check at scaled
volume `t`, then the tail. -/
def gvF (y : TTCState d) (t : NNReal) : Measure (Option (TTCState d)) :=
  (ttcPseudocode.rateCheck (y.removeComponent P) t Th).bind (oldTail Th fuel ν b t)

omit P in
theorem measurable_oldTail_t (y : TTCState d) :
    Measurable fun t : NNReal => oldTail Th fuel ν b t y := by
  unfold oldTail
  exact (Measure.measurable_bind' (measurable_of_countable _)).comp
    (ttc.measurable_poissonMeasure.comp (measurable_id.mul_const _))

omit P in
theorem measurable_rateHalvings (s : TTCState d) :
    Measurable fun t : NNReal => ttcPseudocode.rateHalvings s t Th := by
  unfold ttcPseudocode.rateHalvings
  refine Measurable.ite (measurableSet_le measurable_const (by fun_prop)) ?_ measurable_const
  unfold Real.logb
  exact Nat.measurable_ceil.comp ((Real.measurable_log.comp (by fun_prop)).div_const _)

/-- **The old step after the volume estimate is measurable in the scaled volume.** -/
theorem measurable_gvF (y : TTCState d) : Measurable (gvF P Th fuel ν b y) := by
  classical
  have := ttc.fairCoinStreamLaw_isProbabilityMeasure
  rcases hy : y.removeComponent P with ⟨p', X', nl'⟩
  let Φ : NNReal × ℕ → Measure (Option (TTCState d)) := fun z =>
    fairCoinStreamLaw.bind fun c =>
      oldTail Th fuel ν b z.1 ⟨p' / 2 ^ z.2, samplesAfter c z.2 X', nl'⟩
  have hΦ : Measurable Φ := by
    apply measurable_from_prod_countable_left
    intro k
    let Ψ : NNReal × Finset (ttc.SampleCopy d) → Measure (Option (TTCState d)) := fun z =>
      oldTail Th fuel ν b z.1 ⟨p' / 2 ^ k, z.2, nl'⟩
    have hΨ : Measurable Ψ := by
      refine measurable_from_prod_countable_left fun X => ?_
      exact measurable_oldTail_t Th fuel ν b (⟨p' / 2 ^ k, X, nl'⟩ : TTCState d)
    have hpair : Measurable fun z : NNReal × (ℕ × ℕ → Bool) => (z.1, samplesAfter z.2 k X') :=
      measurable_fst.prodMk ((ttc.measurable_samplesAfter_fixed k X').comp measurable_snd)
    exact ttc.measurable_fixed_sfinite_bind fairCoinStreamLaw
      (fun z : NNReal × (ℕ × ℕ → Bool) => Ψ (z.1, samplesAfter z.2 k X')) (hΨ.comp hpair)
  have heq : gvF P Th fuel ν b y =
      fun t => Φ (t, ttcPseudocode.rateHalvings ⟨p', X', nl'⟩ t Th) := by
    funext t
    rw [gvF, hy, ttcPseudocode.rateCheck, Measure.bind_map
      (measurable_rateCheckResult _ t Th).aemeasurable (aemeasurable_rateCheck Th _ t _)]
    rfl
  rw [heq]
  exact hΦ.comp (measurable_id.prodMk (measurable_rateHalvings Th _))

/-- **The old step with fuel**: CV18's volume estimate, then `gvF` at `t = 10^{bn} · v`. -/
def oldStepF (hn : 3 ≤ d) (eta delta : ℝ) (y : TTCState d) : Measure (Option (TTCState d)) :=
  (ttc.communityCV18VolumeLaw hn P eta delta).bind fun vol =>
    gvF P Th fuel ν b y (ttcPseudocode.t b d vol.2)

theorem measurable_gvF_vol (y : TTCState d) :
    Measurable fun vol : ttc.VolumeOutcome => gvF P Th fuel ν b y (ttcPseudocode.t b d vol.2) :=
  (measurable_gvF P Th fuel ν b y).comp (by unfold ttcPseudocode.t; fun_prop)

end OldStep

/-! ## The sealed step, piece by piece -/

section NewStep

variable {Q : Type} [MeasurableSpace Q]

theorem mf_rateT (thresh : Num ℝ) (L : Loaded d) (scaled : Fin L.facets → Num ℝ)
    {t : Q → Num ℝ} (ht : Measurable t) (x : State d) :
    MeasFam fun q => rateT thresh L scaled (t q) x := by
  unfold rateT
  refine MeasFam.bind' (mf_filterCopies (keep := fun _ z => memDel L scaled z) ?_
    measurable_const) ?_
  · unfold memDel
    exact MeasFam.compute (mp_latticeMember L _ measurable_snd)
      (MeasFam.pure (g := fun p : (Q × (Fin d → Num ℤ)) × Bool => !p.2)
        ((measurable_of_countable (fun b : Bool => !b)).comp measurable_snd))
  refine MeasFam.compute (mp_mul (ht.comp (by fun_prop)) measurable_const) ?_
  refine MeasFam.compute (mp_le measurable_const measurable_snd) ?_
  refine MeasFam.iteB measurable_snd ?_ (MeasFam.pure ?_)
  · apply MeasFam.compute
    · unfold rateProg
      refine MP.bind' (mp_div (by fun_prop) measurable_const) ?_
      refine MP.bind' (mp_log measurable_snd) ?_
      refine MP.bind' (MP.const _) ?_
      refine MP.bind' (mp_log measurable_snd) ?_
      refine MP.bind' (mp_div (by fun_prop) measurable_snd) ?_
      refine MP.bind' (mp_ceil measurable_snd) ?_
      refine MP.bind' (mp_powHeld (by fun_prop) measurable_snd) ?_
      refine MP.bind' (mp_div measurable_const measurable_snd) ?_
      refine MP.bind' (MP.const _) ?_
      refine MP.bind' (mp_div measurable_snd (by fun_prop)) ?_
      exact MP.pure (by fun_prop)
    apply MeasFam.bind'
    · apply mf_filterCopies
      · refine MeasFam.unitT ?_
        exact MeasFam.computeEnd (mp_lt measurable_snd (by fun_prop))
      · fun_prop
    · exact MeasFam.pure (by fun_prop)
  · exact measurable_const.prodMk (by fun_prop)

theorem mf_tailT (fuel : ℕ) (K : Params) (L : Loaded d) (scaled : Fin L.facets → Num ℝ)
    {t : Q → Num ℝ} (ht : Measurable t) {q : Q → Num ℝ × List (Fin d → Num ℤ) × Num ℕ}
    (hq : Measurable q) : MeasFam fun a => tailT fuel K L (t a) scaled (q a) := by
  unfold tailT
  refine MeasFam.compute (mp_mul ht (measurable_fst.comp hq)) ?_
  refine MeasFam.poissonT measurable_snd ?_
  apply MeasFam.bind'
  · apply mf_halve <;> fun_prop
  exact mf_sampleT fuel K L scaled measurable_snd

theorem free_rateT (thresh : Num ℝ) (L : Loaded d) (scaled : Fin L.facets → Num ℝ) (t : Num ℝ)
    (x : State d) : Free (rateT thresh L scaled t x) := by
  unfold rateT
  refine Free.bind (free_filterCopiesT (fun z => Free.bind (free_compute _) fun _ => free_pure _) _)
    fun r => Free.bind (free_compute _) fun _ => Free.bind (free_compute _) fun big => ?_
  refine free_ite _ ?_ (free_pure _)
  refine Free.bind (free_compute _) fun y => Free.bind (free_filterCopiesT (fun _ =>
    Free.bind free_unitT fun _ => free_compute _) _) fun _ => free_pure _

theorem free_sampleT (fuel : ℕ) (K : Params) (L : Loaded d) (scaled : Fin L.facets → Num ℝ)
    (h : Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ) : Free (sampleT fuel K L scaled h) := by
  unfold sampleT
  refine Free.bind (free_compute _) fun W => ?_
  refine Free.bind ?_ fun _ => free_pure _
  exact free_loopRounds (fun y => Free.bind (free_sampleUntilAcceptedT _ _ _ _ _) fun z =>
    Free.bind (free_compute _) fun _ => Free.bind (free_compute _) fun _ => free_pure _) _ _

theorem free_tailT (fuel : ℕ) (K : Params) (L : Loaded d) (t : Num ℝ)
    (scaled : Fin L.facets → Num ℝ) (q : Num ℝ × List (Fin d → Num ℤ) × Num ℕ) :
    Free (tailT fuel K L t scaled q) := by
  rw [tailT_eq]
  exact Free.bind (free_compute _) fun rate => Free.bind (free_poissonT _) fun N =>
    Free.bind (free_halveT K fuel _ _ _ _) fun h => free_sampleT fuel K L scaled h

/-- The rate check keeps `p ≥ 0` and the count equal to the list's length. -/
theorem post_rateT (thresh : Num ℝ) (L : Loaded d) (scaled : Fin L.facets → Num ℝ) (t : Num ℝ)
    (x : State d) (hp : 0 ≤ x.p.get) :
    Post (rateT thresh L scaled t x) fun q => 0 ≤ q.1.get ∧ q.2.2.get = q.2.1.length := by
  unfold rateT
  refine Post.bind ((post_filterCopiesT _ x.X).mono fun r hr => ?_)
  refine post_compute_bind (post_compute_bind ?_)
  refine post_ite _ ?_ ⟨hp, hr⟩
  refine post_compute_bind (Post.bind ((post_filterCopiesT _ r.1).mono fun r' hr' => ?_))
  refine ⟨?_, hr'⟩
  show 0 ≤ (rateProg _ thresh x.p).val.1.get
  rw [(rateProg_val _ thresh x.p).1]
  positivity

end NewStep

/-! ## A continuation that leaves the cap alone -/

section FreeCont

variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

omit [MeasurableSpace α] in
theorem exec_fst_of_free {p : Tree d α} (hp : Free p) (b b' : ℕ) (t : Tape d) :
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
  | setBudget c k ih => exact hp.elim
  | spend k ih => exact hp.elim

/-- **A tree that leaves the cap alone has the same result law for every cap.** -/
theorem vlaw_eq_of_free {p : Tree d α} (hp : Free p)
    (hm : ∀ c, Measurable fun t => outcome (exec p c t)) (b b' : ℕ) : vlaw p b = vlaw p b' := by
  rw [vlaw, vlaw, ← tapeLaw_map_exec p b (hm b), ← tapeLaw_map_exec p b' (hm b'),
    Measure.map_map measurable_fst (hm b), Measure.map_map measurable_fst (hm b')]
  congr 1
  funext t
  exact exec_fst_of_free hp b b' t

/-- **A sequence whose continuation leaves the cap alone**, at any cap for the continuation. -/
theorem vlaw_bind_freeCont {f : α → Tree d β} (hf : MeasFam f) (hfree : ∀ a, Free (f a))
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
    exact vlaw_eq_of_free (hfree a) (fun c' => hf.outcome a c') b' c

end FreeCont

end ttc.Tape
