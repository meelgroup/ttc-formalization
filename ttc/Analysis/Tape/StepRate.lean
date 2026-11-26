/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Corr

/-!
# One step, part one: the deletion pass and the rate check

The sealed step removes the stored copies lying in the component, then, if `t p ≥ Thresh`,
keeps each copy with probability `2^{-k}` for `k = ⌈log₂(t p / Thresh)⌉` and divides `p` by
`2^k`.  The old step does the same with `k` fair rounds of its coin stream
(`ttcPseudocode.rateCheck` after `TTCState.removeComponent`).  Read through the state
views, the two have the same law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree
open ttc (TTCState samplesAfter survives fairCoinStreamLaw fairCoinLaw)
open ArlibCommunity.Algorithms.CV18 (measurable_some)

variable {d : ℕ}

/-! ## Survivors as a selection -/

section Survivors

theorem labelSurvives_iff (coins : ℕ × ℕ → Bool) (k ℓ : ℕ) :
    ttc.labelSurvives k (fun r => coins (r, ℓ)) = true ↔ survives coins k ℓ := by
  classical
  unfold ttc.labelSurvives survives
  split_ifs with h
  · simpa using h
  · simpa using h

variable (Ls : List (ttc.SampleCopy d))

theorem samplesAfter_eq_keepSet (X : Finset (ttc.SampleCopy d)) (hX : Ls.toFinset = X)
    (coins : ℕ × ℕ → Bool) (k : ℕ) :
    samplesAfter coins k X = keepSet Ls (fun i => ttc.labelSurvives k (fun r => coins (r, (Ls.get i).1))) := by
  classical
  ext copy
  simp only [samplesAfter, Finset.mem_filter, keepSet, List.mem_toFinset, mem_selectBy,
    labelSurvives_iff, ← hX]
  constructor
  · rintro ⟨hc, h0⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hc
    exact ⟨i, hi, by rw [hi]; exact h0⟩
  · rintro ⟨i, hi, h0⟩
    exact ⟨List.mem_iff_get.mpr ⟨i, hi⟩, by rw [← hi]; exact h0⟩

/-- **Distinct copies survive `k` fair rounds independently, each with probability `2^{-k}`.** -/
theorem survivors_law (hlab : (Ls.map (·.1)).Nodup) (k : ℕ) :
    fairCoinStreamLaw.map (fun coins => fun i : Fin Ls.length =>
      ttc.labelSurvives k (fun r => coins (r, (Ls.get i).1))) =
      Measure.pi fun _ : Fin Ls.length => bernoulliMeasure true false (ttc.survivalProbability k) := by
  have hP : ∀ _ : ℕ, IsProbabilityMeasure
      ((Measure.infinitePi fun _ : ℕ => fairCoinLaw).map (ttc.labelSurvives k)) := by
    intro _
    rw [ttc.labelStreamLaw_survivalProbability]
    infer_instance
  have hinj : Function.Injective fun i : Fin Ls.length => (Ls.get i).1 := by
    intro i j h
    have hinj := List.nodup_iff_injective_get.mp hlab
    have := hinj (a₁ := ⟨i, by simp⟩) (a₂ := ⟨j, by simp⟩) (by simpa using h)
    exact Fin.ext (by simpa using congrArg Fin.val this)
  have hvec : Measurable fun coins : ℕ × ℕ → Bool =>
      fun label => ttc.labelSurvives k (fun r => coins (r, label)) :=
    Measurable.of_eval fun label => (ttc.measurable_labelSurvives k).comp
      (Measurable.of_eval fun r => measurable_pi_apply (r, label))
  have hfun : (fun coins : ℕ × ℕ → Bool => fun i : Fin Ls.length =>
      ttc.labelSurvives k (fun r => coins (r, (Ls.get i).1))) =
      (fun v : ℕ → Bool => fun i : Fin Ls.length => v (Ls.get i).1) ∘
        fun coins label => ttc.labelSurvives k (fun r => coins (r, label)) := by
    funext coins i
    rfl
  rw [hfun, ← Measure.map_map (measurable_pi_iff.mpr fun i => measurable_pi_apply _) hvec,
    ttc.fairCoinStreamLaw_survivalVector k, Measure.map_infinitePi_infinitePi_of_inj hinj,
    Measure.infinitePi_eq_pi]
  simp only [ttc.labelStreamLaw_survivalProbability]

end Survivors


/-! ## The deletion pass -/

section Deletion

/-- **The filter with answers that read no tape**: the copies kept are those whose answer
is `true`. -/
theorem exec_foldlM_filterStep_det {keep : (Fin d → Num ℤ) → Tree d Bool}
    {κ : (Fin d → Num ℤ) → Bool}
    (hkeep : ∀ x b t, ∃ j, exec (keep x) b t = (some (κ x), j, b, t))
    (one : Num ℕ) (hone : one.get = 1) :
    ∀ (X : List (Fin d → Num ℤ)) (acc : List (Fin d → Num ℤ) × Num ℕ) (b : ℕ) (t : Tape d),
      Option.map (fun r : List (Fin d → Num ℤ) × Num ℕ => (r.1, r.2.get))
          (exec (X.foldlM (filterStep keep one) acc) b t).1 =
        some (acc.1 ++ X.filter κ, acc.2.get + (X.filter κ).length)
  | [], acc, b, t => by simp [exec]
  | x :: xs, acc, b, t => by
      rw [List.foldlM_cons]
      show Option.map _ (exec ((filterStep keep one acc x).bind _) b t).1 = _
      rw [exec_bind]
      have hstep : exec (filterStep keep one acc x) b t =
          ((some (if κ x then (acc.1 ++ [x], (A.add acc.2 one).val) else acc)),
            (exec (filterStep keep one acc x) b t).2.1, b, t) := by
        obtain ⟨j', hj'⟩ := hkeep (A.cell x).val b t
        simp only [filterStep, compute, Tree.bind, exec]
        rw [exec_bind, hj']
        have hx : (A.cell x).val = x := rfl
        rw [hx]
        cases κ x <;> simp [exec, A.push, ttc.Model.Operations.push]
      rw [hstep]
      simp only
      rw [exec_foldlM_filterStep_det hkeep one hone xs]
      cases h : κ x
      · simp [List.filter_cons, h]
      · simp only [List.filter_cons, h, ite_true, List.length_cons, A.add, Num.get_add, hone,
          List.append_assoc, List.singleton_append]
        congr 2
        omega

theorem filter_map_rel {α β γ : Type} (f : α → γ) (g : β → γ) (κ₁ : α → Bool) (κ₂ : β → Bool) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.map f = l₂.map g →
      (∀ x ∈ l₁, ∀ y ∈ l₂, f x = g y → κ₁ x = κ₂ y) →
      (l₁.filter κ₁).map f = (l₂.filter κ₂).map g
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: l₁, y :: l₂, h, hk => by
      simp only [List.map_cons, List.cons.injEq] at h
      have ih := filter_map_rel f g κ₁ κ₂ l₁ l₂ h.2
        (fun x' hx' y' hy' => hk x' (List.mem_cons_of_mem _ hx') y' (List.mem_cons_of_mem _ hy'))
      have hxy := hk x (List.mem_cons_self ..) y (List.mem_cons_self ..) h.1
      simp only [List.filter_cons, hxy]
      split_ifs
      · simp [h.1, ih]
      · exact ih

end Deletion


section Member

/-- **The deletion test**: the sealed membership test of a stored copy's integer point in
`10^b · P` is the old membership test of its decoded point in `P`. -/
theorem latticeMember_copy (P : ttc.PolytopeData d) (b : ℕ) (scale : Num ℝ)
    (hs : scale.get = ttc.decimalScale b) (c : ttc.SampleCopy d) (hc : c.2.1 = b) :
    (latticeMember (loaded P) (scaledOffsets (loaded P) scale).val (sealZ c.2.2)).val =
      (P.presentation.memberProg c.2.toPoint).value := by
  have hpos : 0 < ttc.decimalScale b := by unfold ttc.decimalScale; positivity
  rw [Bool.eq_iff_iff]
  change accepts (loaded P) (scaledOffsets (loaded P) scale).val c.2.2 = true ↔ _
  rw [accepts_iff P b scale hs, ttc.acceptedIntegers, Set.mem_setOf_eq,
    ttc.HalfspacePresentation.memberProg, ttc.HalfspacePresentation.memberProg,
    ttc.Counted.allFacets_value, ttc.Counted.allFacets_value]
  simp only [ttc.PolytopeData.scaledPresentation, ttc.PolytopeData.scaledOffsetsProg,
    ttc.Counted.forEach, ttc.Counted.mul, ttc.LatticePoint.toPoint, hc]
  refine forall_congr' fun j => ?_
  have hdot : dotProduct (P.presentation.normal j) c.2.toPoint =
      dotProduct (P.presentation.normal j) (fun i => (c.2.2 i : ℝ)) / ttc.decimalScale b := by
    simp only [dotProduct, ttc.LatticePoint.toPoint, hc, ttc.decimalScale, Finset.sum_div,
      mul_div_assoc]
  rw [hdot, div_le_iff₀ hpos, mul_comm]

end Member


/-! ## Trees that read no tape -/

section StepOnly

/-- A tree made only of computation steps. -/
def StepOnly {α : Type} : Tree d α → Prop
  | .pure _ => True
  | .step c k => StepOnly (k c.val)
  | _ => False

theorem StepOnly.bind {α β : Type} {p : Tree d α} {f : α → Tree d β} (hp : StepOnly p)
    (hf : ∀ a, StepOnly (f a)) : StepOnly (p.bind f) := by
  induction p with
  | pure a => exact hf a
  | step c k ih => exact ih c.val hp
  | _ => exact hp.elim

theorem stepOnly_compute {α : Type} (c : Prog α) : StepOnly (compute (n := d) c) := trivial
theorem stepOnly_pure {α : Type} (a : α) : StepOnly (Tree.pure (n := d) a) := trivial

theorem stepOnly_ite {α : Type} (c : Bool) {p q : Tree d α} (hp : StepOnly p) (hq : StepOnly q) :
    StepOnly (if c then p else q) := by cases c <;> assumption

theorem stepOnly_foldlM {β ι : Type} {g : β → ι → Tree d β} (hg : ∀ b x, StepOnly (g b x)) :
    ∀ (l : List ι) (b : β), StepOnly (l.foldlM g b)
  | [], b => trivial
  | x :: l, b => by
      simp only [List.foldlM_cons]
      exact StepOnly.bind (hg b x) fun b' => stepOnly_foldlM hg l b'

/-- **A tree that reads no tape passes its value on.** -/
theorem vlaw_bind_stepOnly {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {p : Tree d α}
    (hp : StepOnly p) {a : α} (ha : ∀ b t, (exec p b t).1 = some a) (f : α → Tree d β) (b : ℕ) :
    vlaw (p.bind f) b = vlaw (f a) b := by
  induction p with
  | pure a' =>
      have : a' = a := Option.some.inj ((ha 0 (fun _ => default)))
      subst this
      rfl
  | step c k ih =>
      show vlaw (Tree.step c fun x => (k x).bind f) b = _
      rw [vlaw_step]
      exact ih c.val hp (fun b t => ha b t)
  | _ => exact hp.elim

theorem stepOnly_filterCopiesT {keep : (Fin d → Num ℤ) → Tree d Bool} (hk : ∀ x, StepOnly (keep x))
    (X : List (Fin d → Num ℤ)) : StepOnly (filterCopiesT keep X) :=
  stepOnly_foldlM (fun acc x => StepOnly.bind (stepOnly_compute _) fun x' =>
    StepOnly.bind (hk x') fun k => stepOnly_ite k (StepOnly.bind (stepOnly_compute _) fun _ =>
      StepOnly.bind (stepOnly_compute _) fun _ => stepOnly_pure _) (stepOnly_pure _)) X _

end StepOnly


/-! ## The rate check -/

section Rate

/-- The rate check's arithmetic: `k = ⌈log₂(t p / Thresh)⌉`, `p / 2^k` and `2^{-k}`. -/
noncomputable def rateProg (tp thresh p : Num ℝ) : Prog (Num ℝ × Num ℝ) := do
  let ratio ← A.div tp thresh
  let lr ← A.log ratio
  let two ← A.lit (2 : ℝ)
  let l2 ← A.log two
  let kR ← A.div lr l2
  let k ← A.ceil kR
  let twoK ← powHeld two k
  let p' ← A.div p twoK
  let one ← A.lit (1 : ℝ)
  let keepProb ← A.div one twoK
  A.pure (p', keepProb)

/-- The deletion test as the step uses it. -/
def memDel (L : Loaded d) (scaled : Fin L.facets → Num ℝ) (x : Fin d → Num ℤ) : Tree d Bool :=
  (compute (latticeMember L scaled x)).bind fun inside => .pure (!inside)

/-- **The deletion pass and the rate check**, as the step runs them. -/
def rateT (thresh : Num ℝ) (L : Loaded d) (scaled : Fin L.facets → Num ℝ) (t : Num ℝ)
    (s : State d) : Tree d (Num ℝ × List (Fin d → Num ℤ) × Num ℕ) :=
  (filterCopiesT (memDel L scaled) s.X).bind fun r =>
  (compute (A.mul t s.p)).bind fun tp =>
  (compute (A.le thresh tp)).bind fun big =>
  if big then
    (compute (rateProg tp thresh s.p)).bind fun y =>
    (filterCopiesT (fun _ => unitT.bind fun u => compute (A.lt u y.2)) r.1).bind fun r' =>
    .pure (y.1, r'.1, r'.2)
  else .pure (s.p, r.1, r.2)

theorem get_powHeld_two (k : Num ℕ) :
    (powHeld (A.lit (2 : ℝ)).val k).val.get = (2 : ℝ) ^ k.get := by
  simp only [powHeld, Charged.val_bind, A.cast, A.log, A.mul, A.exp, A.lit, Num.get_exp,
    Num.get_mul, Num.get_log, Num.get_cast, Num.get_lit]
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem rateProg_val (tp thresh p : Num ℝ) :
    let k := Nat.ceil (Real.log (tp.get / thresh.get) / Real.log 2)
    (rateProg tp thresh p).val.1.get = p.get / 2 ^ k ∧
      (rateProg tp thresh p).val.2.get = ((1 : ℝ) / 2) ^ k := by
  intro k
  have h := get_powHeld_two (A.ceil (A.div (A.log (A.div tp thresh).val).val
    (A.log (A.lit (2 : ℝ)).val).val).val).val
  simp only [A.ceil, A.div, A.log, A.lit, Num.get_ceil, Num.get_div, Num.get_log, Num.get_lit] at h
  simp only [rateProg, Charged.val_bind, val_Apure, A.div, Num.get_div, A.lit, Num.get_lit]
  refine ⟨?_, ?_⟩
  · simp only [A.ceil, A.div, A.log, A.lit, Num.get_ceil, Num.get_div, Num.get_log, Num.get_lit] at *
    rw [h]
  · simp only [A.ceil, A.div, A.log, A.lit, Num.get_ceil, Num.get_div, Num.get_log, Num.get_lit] at *
    rw [h, one_div_pow]

end Rate


section RateHelpers

theorem vlaw_filterCopiesT_below' (q : Num ℝ) (h0 : 0 ≤ q.get) (h1 : q.get ≤ 1)
    (X : List (Fin d → Num ℤ)) (b : ℕ) :
    vlaw (filterCopiesT (fun _ => unitT.bind fun u => compute (A.lt u q)) X) b =
      ((Measure.pi fun _ : Fin X.length => bernoulliMeasure true false ⟨q.get, h0, h1⟩).map
        fun c => (selectBy X c, (sealDraw (selectBy X c).length).val)).map some := by
  have hv : Measurable (Option.map fun r : List (Fin d → Num ℤ) × Num ℕ => (r.1, r.2.get)) :=
    measurable_optionMap (measurable_fst.prodMk (Num.measurable_get.comp measurable_snd))
  have hw : Measurable (Option.map fun r : List (Fin d → Num ℤ) × ℕ => (r.1, (sealDraw r.2).val)) :=
    measurable_optionMap (measurable_fst.prodMk (measurable_sealDraw.comp measurable_snd))
  have h := congrArg (Measure.map (Option.map fun r : List (Fin d → Num ℤ) × ℕ =>
    (r.1, (sealDraw r.2).val))) (vlaw_filterCopiesT_below q h0 h1 X b)
  rw [Measure.map_map hw hv, Measure.map_map hw (measurable_of_countable _)] at h
  have hid : (Option.map fun r : List (Fin d → Num ℤ) × ℕ => (r.1, (sealDraw r.2).val)) ∘
      (Option.map fun r : List (Fin d → Num ℤ) × Num ℕ => (r.1, r.2.get)) = id := by
    funext o
    rcases o with _ | ⟨ys, c⟩
    · rfl
    · simp [sealDraw_get]
  rw [hid, Measure.map_id] at h
  rw [h, Measure.map_map measurable_some (measurable_of_countable _)]
  rfl

theorem pi_map_cast {γ : Type} [MeasurableSpace γ] {a b : ℕ} (h : a = b) (μ : Measure Bool)
    (F : (Fin b → Bool) → γ) :
    (Measure.pi fun _ : Fin b => μ).map F =
      (Measure.pi fun _ : Fin a => μ).map fun c => F (c ∘ Fin.cast h.symm) := by
  subst h
  rfl

theorem keepSet_val (Ls : List (ttc.SampleCopy d)) (hnd : Ls.Nodup) (c : Fin Ls.length → Bool) :
    (keepSet Ls c).val = ((selectBy Ls c : List _) : Multiset _) := by
  classical
  rw [keepSet, List.toFinset_val, List.dedup_eq_self.mpr ((selectBy_sublist Ls c).nodup hnd)]

end RateHelpers


theorem measurable_samplesAfter_rounds (X : Finset (ttc.SampleCopy d)) (k : ℕ) :
    Measurable fun coins : ℕ × ℕ → Bool => samplesAfter coins k X := by
  classical
  rw [measurable_finset_iff]
  intro copy
  apply measurable_to_prop
  by_cases hc : copy ∈ X
  · have : (fun coins : ℕ × ℕ → Bool => copy ∈ samplesAfter coins k X) ⁻¹' {True} =
        {coins | survives coins k copy.1} := by
      ext coins; simp [samplesAfter, hc]
    rw [this]
    exact ttc.measurableSet_survives k copy.1
  · have : (fun coins : ℕ × ℕ → Bool => copy ∈ samplesAfter coins k X) ⁻¹' {True} = ∅ := by
      ext coins; simp [samplesAfter, hc]
    rw [this]
    exact MeasurableSet.empty

theorem measurable_rateCheckResult (s : TTCState d) (t : NNReal) (Th : ℝ) :
    Measurable (ttcPseudocode.rateCheckResult s t Th) := by
  intro S hS
  obtain ⟨T, hT, rfl⟩ := hS
  exact (measurable_const.prodMk ((measurable_samplesAfter_rounds s.X _).prodMk measurable_const)) hT

theorem vlaw_compute_bind {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (c : Prog α)
    (f : α → Tree d β) (b : ℕ) : vlaw ((compute c).bind f) b = vlaw (f c.val) b := by
  show vlaw (Tree.step c f) b = _
  exact vlaw_step c f b

section RatePiece

variable (P : ttc.PolytopeData d) (b : ℕ) (scale thresh t : Num ℝ) (Th : ℝ) (tO : NNReal)

/-- The view of the rate check's result. -/
def triView (q : Num ℝ × List (Fin d → Num ℤ) × Num ℕ) : ℝ × ℕ := stVN ⟨q.1, q.2.1, q.2.2⟩

omit P b scale thresh t Th tO in
theorem measurable_triView : Measurable (triView (d := d)) :=
  (stCorr (d := d) 0).measurable_vN.comp
    (State.measurable_mk measurable_fst (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd))

/-- **The deletion pass and the rate check have the old model's law**, read through the
state views. -/
theorem rate_piece (hs : scale.get = ttc.decimalScale b) (hth : thresh.get = Th)
    (ht : t.get = tO) (hTh : 0 < Th) (x : State d) (y : TTCState d) (hrel : (stCorr b).Rel x y)
    (b' : ℕ) :
    (vlaw (rateT thresh (loaded P) (scaledOffsets (loaded P) scale).val t x) b').map
        (Option.map triView) =
      ((ttcPseudocode.rateCheck (y.removeComponent P) tO Th).map stVO).map some := by
  classical
  obtain ⟨Ls, hXL, hLs, hlab, hbel, hp, hsize⟩ := stCorr_rel_list hrel
  have hnd : Ls.Nodup := List.Nodup.of_map _ hlab
  set scaled := (scaledOffsets (loaded P) scale).val
  set κ : (Fin d → Num ℤ) → Bool := fun z => !(latticeMember (loaded P) scaled z).val
  set oκ : ttc.SampleCopy d → Bool := fun c => decide ((P.presentation.memberProg c.2.toPoint).value = false)
  set Xd := x.X.filter κ
  set Lsd := Ls.filter oκ
  have hXd : Xd.map getZ = Lsd.map (fun c => c.2.2) := by
    refine filter_map_rel getZ (fun c : ttc.SampleCopy d => c.2.2) κ oκ x.X Ls hXL ?_
    intro z _ c hc hzc
    have hcode := (hbel c hc).2
    have := latticeMember_copy P b scale hs c hcode
    rw [← hzc, sealZ_getZ] at this
    show (!(latticeMember (loaded P) scaled z).val) = decide ((P.presentation.memberProg c.2.toPoint).value = false)
    rw [this]
    cases (P.presentation.memberProg c.2.toPoint).value <;> rfl
  have hLsd : Lsd.toFinset = (y.removeComponent P).X := by
    rw [List.toFinset_filter, hLs]
    rfl
  have hndd : Lsd.Nodup := hnd.filter _
  have hlabd : (Lsd.map (·.1)).Nodup := (List.filter_sublist.map _).nodup hlab
  have hlen : Xd.length = Lsd.length := by simpa using congrArg List.length hXd
  -- the deletion pass reads no tape
  have hdet : ∀ b t, (exec (filterCopiesT (memDel (loaded P) scaled) x.X) b t).1 =
      some (Xd, (sealDraw Xd.length).val) := by
    intro b t
    have h := exec_foldlM_filterStep_det (keep := memDel (loaded P) scaled) (κ := κ)
      (fun z b t => ⟨_, rfl⟩) (A.lit (1 : ℕ)).val rfl x.X ([], (A.lit (0 : ℕ)).val) b t
    simp only [List.nil_append, A.lit, Num.get_lit, zero_add] at h
    rcases e : (exec (filterCopiesT (memDel (loaded P) scaled) x.X) b t).1 with _ | ⟨ys, c⟩
    · exact absurd (e ▸ h : Option.map _ none = _) (by simp)
    · have h' : (ys, c.get) = (Xd, Xd.length) := by
        have := e ▸ h
        exact Option.some.inj this
      simp only [Prod.mk.injEq] at h'
      rw [h'.1]
      congr
      exact Num.ext (by rw [h'.2]; rfl)
  have hso : StepOnly (filterCopiesT (memDel (loaded P) scaled) x.X) :=
    stepOnly_filterCopiesT (keep := memDel (loaded P) scaled) (fun z => by
      unfold memDel; exact StepOnly.bind (stepOnly_compute _) fun _ => stepOnly_pure _) x.X
  rw [rateT, vlaw_bind_stepOnly hso hdet]
  rw [vlaw_compute_bind, vlaw_compute_bind]
  have hp' : (y.removeComponent P).p = y.p := rfl
  have hbig : (A.le thresh (A.mul t x.p).val).val = decide (Th ≤ (tO : ℝ) * y.p) := by
    simp [A.le, A.mul, hth, ht, hp]
  rw [hbig]
  have hXv : ((Xd.map getZ : List _) : Multiset (Fin d → ℤ)) =
      (y.removeComponent P).X.val.map fun c => c.2.2 := by
    rw [← hLsd, List.toFinset_val, List.dedup_eq_self.mpr hndd, Multiset.map_coe, hXd]
  have hmR : Measurable (ttcPseudocode.rateCheckResult (y.removeComponent P) tO Th) :=
    measurable_rateCheckResult _ _ _
  have hvO : Measurable (stVO (d := d)) := (stCorr (d := d) b).measurable_vO
  simp only [ttcPseudocode.rateCheck]
  rw [Measure.map_map hvO hmR]
  by_cases hb : Th ≤ (tO : ℝ) * y.p
  · -- the rate check thins
    simp only [hb, decide_true, ite_true]
    rw [vlaw_compute_bind]
    set k := Nat.ceil (Real.log ((tO : ℝ) * y.p / Th) / Real.log 2)
    obtain ⟨hy1, hy2⟩ := rateProg_val (A.mul t x.p).val thresh x.p
    set q := (rateProg (A.mul t x.p).val thresh x.p).val
    simp only [A.mul, Num.get_mul, ht, hp, hth] at hy1 hy2
    have hq0 : 0 ≤ q.2.get := by rw [hy2]; positivity
    have hq1 : q.2.get ≤ 1 := by rw [hy2]; exact pow_le_one₀ (by norm_num) (by norm_num)
    rw [vlaw_bind_of_some (MeasFam.pure (g := fun r' : List (Fin d → Num ℤ) × Num ℕ =>
        (q.1, r'.1, r'.2)) (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))
      (free_filterCopiesT (fun _ => Free.bind free_unitT fun _ => free_compute _) Xd) b'
      ((mf_filterCopies (Q := Unit) (keep := fun _ _ => unitT.bind fun u => compute (A.lt u q.2))
        (MeasFam.unitT (MeasFam.computeEnd (mp_lt measurable_snd measurable_const)))
        (X := fun _ => Xd) measurable_const).outcome () b')
      (vlaw_filterCopiesT_below' q.2 hq0 hq1 Xd b')]
    simp only [vlaw_pure]
    have hF : Measurable fun a : List (Fin d → Num ℤ) × Num ℕ => (some (q.1, a.1, a.2) :
        Option (Num ℝ × List (Fin d → Num ℤ) × Num ℕ)) :=
      measurable_some.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
    rw [Measure.bind_dirac_eq_map _ hF, Measure.map_map (measurable_optionMap measurable_triView) hF,
      Measure.map_map ((measurable_optionMap measurable_triView).comp hF) (measurable_of_countable _)]
    -- the old side: survivors of `k` fair rounds
    have hk : ttcPseudocode.rateHalvings (y.removeComponent P) tO Th = k := by
      simp only [ttcPseudocode.rateHalvings, hp', NNReal.coe_mul, hb, ite_true, Real.logb, k]
    have hsv : Measurable fun coins : ℕ × ℕ → Bool => fun i : Fin Lsd.length =>
        ttc.labelSurvives k (fun r => coins (r, (Lsd.get i).1)) :=
      measurable_pi_iff.mpr fun i => (ttc.measurable_labelSurvives k).comp
        (Measurable.of_eval fun r => measurable_pi_apply _)
    have hold : (fairCoinStreamLaw.map
        (stVO ∘ ttcPseudocode.rateCheckResult (y.removeComponent P) tO Th)) =
        (Measure.pi fun _ : Fin Lsd.length => bernoulliMeasure true false (ttc.survivalProbability k)).map
          fun c : Fin Lsd.length → Bool => (((y.p / 2 ^ k : NNReal) : ℝ),
            encMS ((selectBy Lsd c).map fun c => c.2.2 : Multiset (Fin d → ℤ))) := by
      have hfun : (stVO ∘ ttcPseudocode.rateCheckResult (y.removeComponent P) tO Th) =
          (fun c : Fin Lsd.length → Bool => (((y.p / 2 ^ k : NNReal) : ℝ),
            encMS ((selectBy Lsd c).map fun c => c.2.2 : Multiset (Fin d → ℤ)))) ∘
            fun coins => fun i : Fin Lsd.length =>
              ttc.labelSurvives k (fun r => coins (r, (Lsd.get i).1)) := by
        funext coins
        simp only [Function.comp_apply, stVO, ttcPseudocode.rateCheckResult, hk, hp',
          samplesAfter_eq_keepSet Lsd _ hLsd coins k, keepSet_val Lsd hndd, Multiset.map_coe]
      rw [hfun, ← Measure.map_map (measurable_of_countable _) hsv, survivors_law Lsd hlabd k]
    rw [hold, ← bernoulli_survivalProbability k (by positivity)
        (pow_le_one₀ (by norm_num) (by norm_num)), Measure.map_map measurable_some (measurable_of_countable _),
      pi_map_cast hlen]
    have hB : bernoulliMeasure true false (⟨q.2.get, hq0, hq1⟩ : unitInterval) =
        bernoulliMeasure true false ⟨((1 : ℝ) / 2) ^ k, by positivity,
          pow_le_one₀ (by norm_num) (by norm_num)⟩ := by
      congr 1
      exact Subtype.ext hy2
    rw [hB]
    congr 1
    funext c
    simp only [Function.comp_apply, Option.map_some, triView, stVN]
    refine congrArg some (Prod.ext ?_ ?_)
    · show q.1.get = _
      rw [hy1, NNReal.coe_div, NNReal.coe_pow]
      rfl
    · show encMS _ = encMS _
      rw [selectBy_map_rel getZ (fun c : ttc.SampleCopy d => c.2.2) Xd Lsd hlen hXd c]
  · -- no thinning
    simp only [hb, decide_false, Bool.false_eq_true, ite_false, vlaw_pure]
    have hk : ttcPseudocode.rateHalvings (y.removeComponent P) tO Th = 0 := by
      simp only [ttcPseudocode.rateHalvings, hp', NNReal.coe_mul, hb, ite_false]
    have hconst : (stVO ∘ ttcPseudocode.rateCheckResult (y.removeComponent P) tO Th) =
        fun _ => stVO (y.removeComponent P) := by
      funext coins
      simp only [Function.comp_apply, ttcPseudocode.rateCheckResult, hk, pow_zero, div_one,
        samplesAfter_zero]
    have := ttc.fairCoinStreamLaw_isProbabilityMeasure
    rw [hconst, Measure.map_const, measure_univ, one_smul, Measure.map_dirac' measurable_some,
      Measure.map_dirac' (measurable_optionMap measurable_triView)]
    simp only [Option.map_some, triView, stVN, stVO, hp', hp, hXv]
end RatePiece

end ttc.Tape
