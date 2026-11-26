/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Post

/-!
# One step, part three: Poisson, halving, samples

After the rate check the step draws `N ~ Poisson(t p)`, runs the halving loop with `fuel`
rounds, and appends `N` sampler draws.  The old model's counterpart with the same fuel
(`oldTail`) runs the old second loop truncated at `fuel` rounds (`oldLaw`) and appends the
draws with fresh labels (`addList`).  Read through the state views, the two have the same law
(`tail_piece`).
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

/-! ## The old side -/

section Old

/-- `X.Append(S)` for a list of points, at precision `b`. -/
def addList (b : ℕ) (s : TTCState d) (zs : List (Fin d → ℤ)) : TTCState d :=
  s.addBatch (fun i : Fin zs.length => ((b, zs.get i) : ttc.LatticePoint d))

theorem measurable_addList (b : ℕ) (zs : List (Fin d → ℤ)) :
    Measurable fun s : TTCState d => addList b s zs :=
  ttc.measurable_addBatch.comp (measurable_id.prodMk measurable_const)

theorem measurable_optionAddList (b : ℕ) :
    Measurable fun q : TTCState d × Option (List (Fin d → ℤ)) => q.2.map (addList b q.1) := by
  apply measurable_from_prod_countable_left
  intro o
  rcases o with _ | zs
  · exact measurable_const
  · exact (ArlibCommunity.Algorithms.CV18.measurable_some).comp (measurable_addList b zs)

/-- The points of the copies after appending. -/
theorem addList_points (b : ℕ) (s : TTCState d) (zs : List (Fin d → ℤ))
    (hs : ∀ c ∈ s.X, c.1 < s.nextLabel) :
    (addList b s zs).X.val.map (fun c => c.2.2) = s.X.val.map (fun c => c.2.2) + (zs : Multiset _) := by
  classical
  set g : Fin zs.length → ttc.SampleCopy d := fun i => (s.nextLabel + i.val, (b, zs.get i))
  have hdisj : Disjoint s.X (Finset.univ.image g) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc'
    have := hs _ hc
    simp only [g] at this
    omega
  have hinj : Function.Injective g := by
    intro i j h
    simp only [g, Prod.mk.injEq] at h
    exact Fin.ext (Nat.add_left_cancel h.1)
  have hX : (addList b s zs).X = s.X.disjUnion (Finset.univ.image g) hdisj := by
    rw [Finset.disjUnion_eq_union]
    rfl
  rw [hX, Finset.disjUnion_val, Multiset.map_add, Finset.image_val_of_injOn hinj.injOn,
    Multiset.map_map, Fin.univ_val_map]
  congr 1
  simp only [Function.comp_def, g]
  exact congrArg _ (List.ofFn_get zs)

/-- One draw per pending copy, appended with fresh labels. -/
def sampleKernel (ν : Measure (Option (Fin d → ℤ))) (b : ℕ) (sec : TTCState d × ℕ) :
    Measure (Option (TTCState d)) :=
  (seqLaw ν sec.2).map (Option.map (addList b sec.1))

theorem isProbabilityMeasure_seqLaw (ν : Measure (Option (Fin d → ℤ))) [IsProbabilityMeasure ν] :
    ∀ k, IsProbabilityMeasure (seqLaw ν k)
  | 0 => by rw [seqLaw]; infer_instance
  | k + 1 => by
      have := isProbabilityMeasure_seqLaw ν k
      rw [seqLaw]
      refine isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable (ae_of_all _ ?_)
      rintro (_ | z)
      · simp only [Option.elim]; infer_instance
      · exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem measurable_sampleKernel (ν : Measure (Option (Fin d → ℤ))) [IsProbabilityMeasure ν]
    (b : ℕ) : Measurable (sampleKernel ν b) := by
  apply measurable_from_prod_countable_left
  intro k
  have := isProbabilityMeasure_seqLaw ν k
  have : (fun s : TTCState d => sampleKernel ν b (s, k)) =
      fun s => ((seqLaw ν k).map (Prod.mk s)).map fun q => q.2.map (addList b q.1) := by
    funext s
    rw [Measure.map_map (measurable_optionAddList b) measurable_prodMk_left]
    rfl
  rw [this]
  exact (Measure.measurable_map _ (measurable_optionAddList b)).comp Measurable.map_prodMk_left

/-- **The old step after the rate check, with `fuel`**: `N ~ Poisson(t p)`, the second loop
truncated at `fuel` rounds, then a draw from `ν` for each pending copy. -/
def oldTail (Th : ℝ) (fuel : ℕ) (ν : Measure (Option (Fin d → ℤ))) (b : ℕ) (t : NNReal)
    (y : TTCState d) : Measure (Option (TTCState d)) :=
  (ttc.Poisson (t * y.p)).bind fun N =>
    (oldLaw Th fuel y N).bind fun o => o.elim (Measure.dirac none) (sampleKernel ν b)

/-- The old state invariant: fresh labels and precision `b`. -/
def StInv (b : ℕ) (s : TTCState d) : Prop := s.LabelsFresh ∧ ∀ c ∈ s.X, c.2.1 = b

theorem measurableSet_stInv (b : ℕ) : MeasurableSet {s : TTCState d | StInv b s} := by
  let good : Set (Finset (ttc.SampleCopy d) × ℕ) :=
    {x | ((∀ c ∈ x.1, c.1 < x.2) ∧ (∀ c ∈ x.1, ∀ c' ∈ x.1, c.1 = c'.1 → c = c')) ∧
      ∀ c ∈ x.1, c.2.1 = b}
  have hgood : MeasurableSet good := good.to_countable.measurableSet
  have hpair : Measurable (fun s : TTCState d => (s.X, s.nextLabel)) :=
    measurable_snd.comp (comap_measurable (fun s : TTCState d => (s.p, s.X, s.nextLabel)))
  convert hgood.preimage hpair using 1
  ext s
  rfl

theorem oldLaw_inv (Th : ℝ) (f : ℕ) (s : TTCState d) (N b : ℕ) (hs : StInv b s) :
    ∀ᵐ o ∂oldLaw Th f s N, ∀ a ∈ o, StInv b a.1 := by
  classical
  have hm : MeasurableSet {a : TTCState d × ℕ | StInv b a.1} :=
    measurable_fst (measurableSet_stInv b)
  rw [oldLaw, ae_map_iff (measurable_oldTrunc Th f s N).aemeasurable (measurableSet_forall_mem hm)]
  refine ae_of_all _ fun c a ha => ?_
  simp only [oldTrunc] at ha
  split_ifs at ha
  swap
  · cases ha
  cases ha
  refine ⟨ttc.thinningResult_labelsFresh s N Th c hs.1, fun c' hc' => hs.2 c' ?_⟩
  exact (Finset.mem_filter.mp hc').1

end Old

/-! ## Halving outputs correspond -/

section HalvCorr

/-- **The correspondence of the halving loop's results**: `p`, the multiset of points and the
pending count. -/
def halvCorr (b : ℕ) :
    Corr (Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ) (TTCState d × ℕ) (ℝ × ℕ × ℕ) where
  vN r := (r.1.get, encMS ((r.2.1.map getZ : List _) : Multiset (Fin d → ℤ)), r.2.2.2.get)
  vO r := ((r.1.p : ℝ), encMS (r.1.X.val.map fun c => c.2.2), r.2)
  invN r := 0 ≤ r.1.get
  invO r := StInv b r.1
  secN w := ((stSec (d := d) (w.1, w.2.1)).p, (stSec (d := d) (w.1, w.2.1)).X,
    (stSec (d := d) (w.1, w.2.1)).size, (sealDraw w.2.2).val)
  measurable_vN := by
    refine (Num.measurable_get.comp measurable_fst).prodMk ?_
    refine Measurable.prodMk ?_
      (Num.measurable_get.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    have hL : Measurable fun l : List (Fin d → Num ℤ) =>
        encMS ((l.map getZ : List _) : Multiset (Fin d → ℤ)) := by
      have := measurable_of_ofFn (X := Unit) (α := Fin d → Num ℤ)
        (F := fun p => encMS ((p.2.map getZ : List _) : Multiset (Fin d → ℤ)))
        (fun k => measurable_of_countable _)
      exact this.comp ((measurable_const (a := ())).prodMk measurable_id)
    exact hL.comp (measurable_fst.comp measurable_snd)
  measurable_vO := by
    have hst : Measurable fun s : TTCState d => (s.p, s.X, s.nextLabel) :=
      Measurable.of_comap_le le_rfl
    refine ((measurable_coe_nnreal_real.comp (measurable_fst.comp hst)).comp measurable_fst).prodMk
      ((((measurable_of_countable (fun X : Finset (ttc.SampleCopy d) =>
        encMS (X.val.map fun c => c.2.2))).comp ((measurable_fst.comp measurable_snd).comp hst)).comp
          measurable_fst).prodMk measurable_snd)
  measurable_secN := by
    have hsec : Measurable fun w : ℝ × ℕ × ℕ => stSec (d := d) (w.1, w.2.1) :=
      (stCorr (d := d) 0).measurable_secN.comp (measurable_fst.prodMk measurable_snd.fst)
    exact (State.measurable_p.comp hsec).prodMk ((State.measurable_X.comp hsec).prodMk
      ((State.measurable_size.comp hsec).prodMk
        (Tree.measurable_sealDraw.comp measurable_snd.snd)))
  partner := by
    rintro r hr
    obtain ⟨y, hy, hv⟩ := (stCorr (d := d) b).partner ⟨r.1, r.2.1, r.2.2.1⟩ hr
    refine ⟨(y, r.2.2.2.get), hy, ?_⟩
    have hv' : stVO y = stVN (⟨r.1, r.2.1, r.2.2.1⟩ : State d) := hv
    simp only [stVO, stVN, Prod.mk.injEq] at hv'
    exact Prod.ext hv'.1 (Prod.ext hv'.2 rfl)
  sec_spec := by
    rintro y hy
    obtain ⟨h1, h2⟩ := (stCorr (d := d) b).sec_spec y.1 hy
    refine ⟨h1, ?_⟩
    have h2' : stVN (stSec (stVO y.1)) = stVO y.1 := h2
    simp only [stVO, stVN, Prod.mk.injEq] at h2'
    exact Prod.ext h2'.1 (Prod.ext h2'.2 (get_sealDraw _))

theorem halvCorr_option_vN (b : ℕ) :
    (halvCorr (d := d) b).option.vN = viewNew := rfl

theorem halvCorr_option_vO (b : ℕ) :
    (halvCorr (d := d) b).option.vO = viewOld := rfl

end HalvCorr

/-! ## The sealed tail -/

section Tail

/-- **The step after the rate check**, as the step runs it. -/
def tailT (fuel : ℕ) (K : Params) (L : Loaded d) (t : Num ℝ) (scaled : Fin L.facets → Num ℝ)
    (q : Num ℝ × List (Fin d → Num ℤ) × Num ℕ) : Tree d (State d) :=
  (compute (A.mul t q.1)).bind fun rate =>
  (poissonT rate).bind fun N =>
  (halveT K fuel q.1 q.2.1 q.2.2 N).bind fun h =>
  (compute (walkConstantsProg L K.scale K.epsPrime K.dim)).bind fun W =>
  (loopTree (γ := Empty) h.2.2.2 (sampleBody (sampleUntilAcceptedT L W scaled K.dimN fuel))
      (h.2.1, h.2.2.1)).bind fun res =>
  .pure ⟨h.1, (res.elim id Empty.elim).1, (res.elim id Empty.elim).2⟩

/-- The tail after the halving loop. -/
def sampleT (fuel : ℕ) (K : Params) (L : Loaded d) (scaled : Fin L.facets → Num ℝ)
    (h : Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ) : Tree d (State d) :=
  (compute (walkConstantsProg L K.scale K.epsPrime K.dim)).bind fun W =>
  (loopTree (γ := Empty) h.2.2.2 (sampleBody (sampleUntilAcceptedT L W scaled K.dimN fuel))
      (h.2.1, h.2.2.1)).bind fun res =>
  .pure ⟨h.1, (res.elim id Empty.elim).1, (res.elim id Empty.elim).2⟩

theorem free_sampleUntilAcceptedT (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) :
    ∀ fuel, Free (sampleUntilAcceptedT L W scaled dimN fuel)
  | 0 => free_fail
  | fuel + 1 => Free.bind (free_sampleTryT L W scaled dimN) fun r => by
      rcases r with _ | z
      · exact free_sampleUntilAcceptedT L W scaled dimN fuel
      · exact free_pure z

theorem free_halveT (K : Params) :
    ∀ (f : ℕ) (p : Num ℝ) (X : List (Fin d → Num ℤ)) (size N : Num ℕ),
      Free (halveT K f p X size N)
  | 0, _, _, _, _ => free_fail
  | f + 1, p, X, size, N => by
      unfold halveT
      refine Free.bind (free_compute _) fun stop => free_ite _ (free_pure _) ?_
      refine Free.bind (free_filterCopiesT (fun _ => free_coinT) X) fun r => ?_
      refine Free.bind (free_binomT _) fun N' => ?_
      exact Free.bind (free_compute _) fun p' => free_halveT K f _ _ _ _

theorem mf_sampleT {Q : Type} [MeasurableSpace Q] (fuel : ℕ) (K : Params) (L : Loaded d)
    (scaled : Fin L.facets → Num ℝ) {h : Q → Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ}
    (hh : Measurable h) : MeasFam fun q => sampleT fuel K L scaled (h q) := by
  unfold sampleT
  refine MeasFam.computeConst _ ?_
  apply MeasFam.bind'
  · apply MeasFam.loopTree
    · fun_prop
    · refine MeasFam.bind' ((mf_sampleUntilAccepted L _ _ K.dimN fuel).comp
        (φ := fun _ => ()) measurable_const) ?_
      refine MeasFam.compute (mp_push (by fun_prop) measurable_snd) ?_
      apply MeasFam.compute
      · exact MP.bind' (MP.const _) (mp_addN (by fun_prop) measurable_snd)
      exact MeasFam.pure (measurable_inl.comp (by fun_prop))
    · fun_prop
  · refine MeasFam.pure (State.measurable_mk ?_ ?_ ?_)
    · fun_prop
    · exact measurable_fst.comp ((measurable_id.sumElim measurable_from_top).comp measurable_snd)
    · exact measurable_snd.comp ((measurable_id.sumElim measurable_from_top).comp measurable_snd)

variable (fuel : ℕ) (K : Params) (L : Loaded d) (scaled : Fin L.facets → Num ℝ) (b' : ℕ)
  (ν : Measure (Option (Fin d → ℤ)))
  (hν : (vlaw (sampleUntilAcceptedT L (walkConstantsProg L K.scale K.epsPrime K.dim).val scaled
      K.dimN fuel) b').map (Option.map getZ) = ν)

include hν in
/-- **The sampling after the halving loop**: the points appended are `N` draws from `ν`. -/
theorem sampleT_law (h : Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ) :
    (vlaw (sampleT fuel K L scaled h) b').map (Option.map stVN) =
      (seqLaw ν h.2.2.2.get).map (Option.map fun zs =>
        (h.1.get, encMS (((h.2.1.map getZ ++ zs : List _)) : Multiset (Fin d → ℤ)))) := by
  rw [sampleT]
  show (vlaw (Tree.step _ fun W => Tree.step _ fun _ =>
    (loopRounds (sampleBody (sampleUntilAcceptedT L W scaled K.dimN fuel)) h.2.2.2.get
      (h.2.1, h.2.2.1)).bind fun res => Tree.pure _) b').map _ = _
  rw [vlaw_step, vlaw_step]
  set W := (walkConstantsProg L K.scale K.epsPrime K.dim).val
  set S := sampleUntilAcceptedT L W scaled K.dimN fuel
  have hS : ∀ (Q : Type) [MeasurableSpace Q], MeasFam fun _ : Q => S := fun Q _ =>
    mf_sampleUntilAccepted L W scaled K.dimN fuel
  have hfree : Free S := free_sampleUntilAcceptedT L W scaled K.dimN fuel
  have hmk : Measurable fun res : (List (Fin d → Num ℤ) × Num ℕ) ⊕ Empty =>
      (⟨h.1, (res.elim id Empty.elim).1, (res.elim id Empty.elim).2⟩ : State d) :=
    State.measurable_mk measurable_const
      (measurable_fst.comp (measurable_id.sumElim measurable_from_top))
      (measurable_snd.comp (measurable_id.sumElim measurable_from_top))
  have hloopm : Measurable fun t => outcome (exec (loopRounds (sampleBody S) h.2.2.2.get
      (h.2.1, h.2.2.1)) b' t) :=
    (MeasFam.loopRounds (A := Unit) (body := fun _ => sampleBody S) (mf_sampleBody S hS)
      h.2.2.2.get).outcome ((), (h.2.1, h.2.2.1)) b'
  have hfl : Free (loopRounds (sampleBody S) h.2.2.2.get (h.2.1, h.2.2.1)) :=
    free_loopRounds (body := sampleBody S) (fun y => Free.bind hfree fun z =>
      Free.bind (free_compute _) fun _ => Free.bind (free_compute _) fun _ => free_pure _) _ _
  have hvN : Measurable (stVN (d := d)) := (stCorr (d := d) 0).measurable_vN
  rw [vlaw_bind_pure hfl _ hmk b' hloopm,
    Measure.map_map (measurable_optionMap hvN) (measurable_optionMap hmk)]
  have hfac : (Option.map stVN ∘ Option.map fun res : (List (Fin d → Num ℤ) × Num ℕ) ⊕ Empty =>
      (⟨h.1, (res.elim id Empty.elim).1, (res.elim id Empty.elim).2⟩ : State d)) =
      Option.map (fun w : List (Fin d → ℤ) × ℕ =>
        (h.1.get, encMS ((w.1 : List _) : Multiset (Fin d → ℤ)))) ∘ Option.map loopZ := by
    funext o
    rcases o with _ | r
    · rfl
    · rfl
  rw [hfac, ← Measure.map_map (measurable_of_countable _) (measurable_optionMap measurable_loopZ),
    vlaw_loopRounds_sample S hS hfree b' h.2.2.2.get (h.2.1, h.2.2.1), hν,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext o
  rcases o with _ | zs <;> rfl

theorem tailT_eq (t : Num ℝ) (q : Num ℝ × List (Fin d → Num ℤ) × Num ℕ) :
    tailT fuel K L t scaled q = (compute (A.mul t q.1)).bind fun rate =>
      (poissonT rate).bind fun N =>
        (halveT K fuel q.1 q.2.1 q.2.2 N).bind (sampleT fuel K L scaled) := rfl

include hν in
/-- **The step after the rate check has the old law with the same fuel**, read through the
state views. -/
theorem tail_piece [IsProbabilityMeasure ν] (b : ℕ) (t : Num ℝ) (tO : NNReal) (ht : t.get = tO)
    (q : Num ℝ × List (Fin d → Num ℤ) × Num ℕ) (y : TTCState d) (hq0 : 0 ≤ q.1.get)
    (hsz : q.2.2.get = q.2.1.length) (hv : triView q = stVO y) (hy : StInv b y) :
    (vlaw (tailT fuel K L t scaled q) b').map (Option.map stVN) =
      (oldTail K.thresh.get fuel ν b tO y).map (Option.map stVO) := by
  classical
  have hvN : Measurable (stVN (d := d)) := (stCorr (d := d) 0).measurable_vN
  have hvO : Measurable (stVO (d := d)) := (stCorr (d := d) 0).measurable_vO
  have hrel : (stCorr b).Rel (⟨q.1, q.2.1, q.2.2⟩ : State d) y := ⟨hq0, hy, hv⟩
  obtain ⟨Ls, hXL, hLs, hlab, hbel, hp⟩ := stCorr_rel_list hrel
  have hnd : Ls.Nodup := List.Nodup.of_map _ hlab
  have hlenL : q.2.1.length = Ls.length := by simpa using congrArg List.length hXL
  have hrate : Real.toNNReal (A.mul t q.1).val.get = tO * y.p := by
    simp only [A.mul, Num.get_mul, ht]
    rw [show (q.1.get) = (y.p : ℝ) from hp, ← NNReal.coe_mul, Real.toNNReal_coe]
  -- the continuation after the Poisson draw
  have hmfS : ∀ {Q : Type} [MeasurableSpace Q] {h : Q → Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ},
      Measurable h → MeasFam fun x => sampleT fuel K L scaled (h x) :=
    fun hh => mf_sampleT fuel K L scaled hh
  have hmfP : MeasFam fun N : Num ℕ =>
      (halveT K fuel q.1 q.2.1 q.2.2 N).bind (sampleT fuel K L scaled) :=
    MeasFam.bind' (mf_halve K fuel measurable_const measurable_const measurable_const measurable_id)
      (hmfS measurable_snd)
  have hmPo : Measurable fun τ => outcome (exec (poissonT (n := d) (A.mul t q.1).val) b' τ) :=
    (MeasFam.poissonT (A := Unit) (rate := fun _ => (A.mul t q.1).val) measurable_const
      (k := fun _ N => Tree.pure N) (MeasFam.pure measurable_snd)).outcome () b'
  rw [tailT_eq, vlaw_compute_bind, vlaw_bind hmfP (free_poissonT _) b' hmPo, vlaw_poissonT,
    Measure.bind_map (measurable_of_countable _).aemeasurable
      (measurable_optionKernel (hmfP.measurable_vlaw b')).aemeasurable,
    Measure.map_bind (measurable_of_countable _).aemeasurable (measurable_optionMap hvN).aemeasurable,
    hrate, oldTail,
    Measure.map_bind (measurable_of_countable _).aemeasurable (measurable_optionMap hvO).aemeasurable]
  congr 1
  funext k
  simp only [Option.elim_some]
  -- the halving loop, then the samples
  have hmH : Measurable fun τ => outcome (exec (halveT K fuel q.1 q.2.1 q.2.2 (sealDraw k).val) b' τ) :=
    (mf_halve K fuel (Q := Unit) measurable_const measurable_const measurable_const
      measurable_const).outcome () b'
  have hmS : MeasFam (sampleT fuel K L scaled) := hmfS measurable_id
  have hKN := measurable_optionKernel (hmS.measurable_vlaw b')
  have hKO := measurable_optionKernel (measurable_sampleKernel ν b)
  rw [vlaw_bind hmS (free_halveT K fuel _ _ _ _) b' hmH,
    Measure.map_bind hKN.aemeasurable (measurable_optionMap hvN).aemeasurable,
    Measure.map_bind hKO.aemeasurable (measurable_optionMap hvO).aemeasurable]
  refine (halvCorr (d := d) b).option.bind_eq ?_ ?_ (oldLaw_inv _ _ _ _ _ hy)
    ((Measure.measurable_map _ (measurable_optionMap hvN)).comp hKN) ?_
  · rw [halvCorr_option_vN, halvCorr_option_vO]
    have := halveT_eq_oldLaw K b' fuel q.1 q.2.1 q.2.2 (sealDraw k).val y Ls hp hXL
      (by rw [hsz, hlenL]) hLs hlab (fun c hc => (hbel c hc).1)
    rwa [get_sealDraw] at this
  · have hpost := (post_halveT K fuel q.1 q.2.1 q.2.2 (sealDraw k).val hsz hq0).mono
      fun a ha => ha.2
    exact ae_vlaw_post hpost (measurableSet_Ici.preimage (Num.measurable_get.comp measurable_fst))
      b' hmH
  · rintro (_ | h) (_ | sec) ⟨_, hinv, hview⟩
    · simp only [Option.elim]
      rw [Measure.map_dirac' (measurable_optionMap hvN), Measure.map_dirac' (measurable_optionMap hvO)]
      rfl
    · cases hview
    · cases hview
    · simp only [Option.elim]
      have hv' := Option.some.inj hview
      simp only [halvCorr, Prod.mk.injEq] at hv'
      obtain ⟨hp', hX', hN'⟩ := hv'
      have hinv' : StInv b sec.1 := hinv sec rfl
      rw [sampleT_law fuel K L scaled b' ν hν h, sampleKernel,
        Measure.map_map (measurable_optionMap hvO) (measurable_of_countable _), hN']
      congr 1
      funext o
      rcases o with _ | zs
      · rfl
      · simp only [Option.map_some, Function.comp_apply, stVO]
        rw [addList_points b sec.1 zs hinv'.1.1, hp', ← encMS_injective hX', Multiset.coe_add]
        rfl

end Tail

end ttc.Tape
