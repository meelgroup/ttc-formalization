import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ConcreteSourceProduct

/-! Deterministic evaluation of one fixed-level union prefix from the
independent incoming point-count vectors. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

noncomputable def fixedLevelFold
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (steps : List (FixedLevelStep ι)) → (ι → Nat) →
      (Fin steps.length → ι → Nat) → (ι → Nat)
  | [], initial, _ => initial
  | step :: rest, initial, incoming =>
      fixedLevelFold rest
        (fun x => (if x ∈ step.deleted then 0 else initial x) + incoming 0 x)
        (Fin.tail incoming)

theorem fixedLevelFold_nil
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (initial : ι → Nat) (incoming : Fin ([] : List (FixedLevelStep ι)).length → ι → Nat) :
    fixedLevelFold ([] : List (FixedLevelStep ι)) initial incoming = initial := rfl

theorem fixedLevelFold_cons
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (step : FixedLevelStep ι) (rest : List (FixedLevelStep ι))
    (initial : ι → Nat)
    (incoming : Fin (step :: rest).length → ι → Nat) :
    fixedLevelFold (step :: rest) initial incoming =
      fixedLevelFold rest
        (fun x => (if x ∈ step.deleted then 0 else initial x) + incoming 0 x)
        (Fin.tail incoming) := rfl

theorem measurable_fixedLevelFold
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) (initial : ι → Nat) :
    Measurable (fixedLevelFold steps initial) := by
  exact Measurable.of_discrete

/-- The fixed-level recurrence is a Markov kernel in its initial count
vector. This permits independent incoming vectors to be drawn before the
deterministic fold. -/
theorem fixedLevelLaw_bind_initial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) (μ : Measure (ι → Nat)) :
    fixedLevelLaw steps μ =
      μ.bind (fun initial => fixedLevelLaw steps (Measure.dirac initial)) := by
  induction steps generalizing μ with
  | nil =>
      simp [fixedLevelLaw]
  | cons step rest ih =>
      let ν : Measure (ι → Nat) :=
        Measure.pi (fun x : ι =>
          ProbabilityTheory.poissonMeasure (step.incoming x))
      let update : ((ι → Nat) × (ι → Nat)) → (ι → Nat) :=
        fun pair x =>
          (if x ∈ step.deleted then 0 else pair.1 x) + pair.2 x
      let K : (ι → Nat) → Measure (ι → Nat) :=
        fun initial => ν.map (fun fresh => update (initial, fresh))
      have hK : Measurable K := Measurable.of_discrete
      have htail : Measurable (fun state : ι → Nat =>
          fixedLevelLaw rest (Measure.dirac state)) := Measurable.of_discrete
      have hstep (law : Measure (ι → Nat)) :
          (law.prod ν).map update = law.bind K := by
        rw [Measure.prod_eq_bind_map]
        rw [map_bind_measure law
          (fun initial => ν.map (Prod.mk initial)) update
          (Measurable.of_discrete.aemeasurable)
          (Measurable.of_discrete)]
        congr 1
        funext initial
        rw [Measure.map_map (Measurable.of_discrete) measurable_prodMk_left]
        rfl
      have hdirac (initial : ι → Nat) :
          fixedLevelLaw (step :: rest) (Measure.dirac initial) =
          fixedLevelLaw rest (K initial) := by
        change fixedLevelLaw rest
          (((Measure.dirac initial).prod ν).map update) = _
        rw [hstep]
        rw [Measure.dirac_bind hK]
      calc
        fixedLevelLaw (step :: rest) μ =
            fixedLevelLaw rest (μ.bind K) := by
              change fixedLevelLaw rest ((μ.prod ν).map update) = _
              rw [hstep]
        _ = (μ.bind K).bind (fun state =>
            fixedLevelLaw rest (Measure.dirac state)) := ih _
        _ = μ.bind (fun initial =>
            (K initial).bind (fun state =>
              fixedLevelLaw rest (Measure.dirac state))) := by
                rw [Measure.bind_bind hK.aemeasurable htail.aemeasurable]
        _ = μ.bind (fun initial =>
            fixedLevelLaw (step :: rest) (Measure.dirac initial)) := by
              congr 1
              funext initial
              exact (ih (K initial)).symm.trans (hdirac initial).symm

theorem pointCountVector_pi_fin_cons
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : Nat) (law : Fin (m + 1) → Measure (ι → Nat))
    (hprob : ∀ i, IsProbabilityMeasure (law i)) :
    (law 0).bind (fun current =>
      (Measure.pi (fun i : Fin m => law i.succ)).map
        (Fin.cons current)) =
      Measure.pi law := by
  letI : ∀ i, IsProbabilityMeasure (law i) := hprob
  let tail : Measure (Fin m → ι → Nat) :=
    Measure.pi (fun i : Fin m => law i.succ)
  letI : IsProbabilityMeasure tail := inferInstance
  have hcons : Measurable
      (fun pair : (ι → Nat) × (Fin m → ι → Nat) =>
        (Fin.cons pair.1 pair.2 : Fin (m + 1) → ι → Nat)) :=
    Measurable.of_discrete
  have hproduct : ((law 0).prod tail).map
      (fun pair : (ι → Nat) × (Fin m → ι → Nat) =>
        (Fin.cons pair.1 pair.2 : Fin (m + 1) → ι → Nat)) =
      (law 0).bind (fun current => tail.map (Fin.cons current)) := by
    rw [Measure.prod_eq_bind_map]
    rw [map_bind_measure (law 0)
      (fun current => tail.map (Prod.mk current))
      (fun pair : (ι → Nat) × (Fin m → ι → Nat) =>
        (Fin.cons pair.1 pair.2 : Fin (m + 1) → ι → Nat))
      Measurable.of_discrete.aemeasurable hcons]
    congr 1
    funext current
    rw [Measure.map_map hcons measurable_prodMk_left]
    rfl
  rw [← hproduct]
  apply (Measure.pi_eq (μ := law) (μ' :=
    ((law 0).prod tail).map
      (fun pair : (ι → Nat) × (Fin m → ι → Nat) =>
        (Fin.cons pair.1 pair.2 : Fin (m + 1) → ι → Nat))) ?_).symm
  intro sets hsets
  have hpre : (fun pair : (ι → Nat) × (Fin m → ι → Nat) =>
      Fin.cons pair.1 pair.2) ⁻¹' Set.pi Set.univ sets =
      (sets 0) ×ˢ Set.pi Set.univ (fun i : Fin m => sets i.succ) := by
    ext pair
    simp [Set.mem_pi, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  rw [Measure.map_apply hcons (MeasurableSet.univ_pi hsets), hpre]
  rw [Measure.prod_prod (sets 0)
    (Set.pi Set.univ (fun i : Fin m => sets i.succ))]
  rw [Measure.pi_pi]
  rw [Fin.prod_univ_succ]

noncomputable def fixedLevelIncomingLaw
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (step : FixedLevelStep ι) : Measure (ι → Nat) :=
  Measure.pi (fun x : ι =>
    ProbabilityTheory.poissonMeasure (step.incoming x))

theorem fixedLevelIncomingLaw_isProbabilityMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (step : FixedLevelStep ι) :
    IsProbabilityMeasure (fixedLevelIncomingLaw step) := by
  unfold fixedLevelIncomingLaw
  infer_instance

theorem pointCountVector_pi_poisson_zero_eq_dirac
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0) =
      Measure.dirac (fun _ : ι => 0) := by
  classical
  simp_rw [poissonMeasure_zero_eq_dirac]
  apply Measure.ext_of_singleton
  intro counts
  rw [Measure.pi_singleton]
  by_cases hzero : counts = fun _ : ι => 0
  · subst counts
    simp
  · have hi : ∃ i : ι, counts i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hzero
      funext i
      exact h i
    obtain ⟨i, hi⟩ := hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [hzero]

set_option maxHeartbeats 1200000 in
theorem fixedLevelFold_pi_eq_fixedLevelLaw
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (steps : List (FixedLevelStep ι)) (initial : ι → Nat) :
    (Measure.pi (fun i : Fin steps.length =>
      fixedLevelIncomingLaw (steps.get i))).map
        (fixedLevelFold steps initial) =
      fixedLevelLaw steps (Measure.dirac initial) := by
  induction steps generalizing initial with
  | nil =>
      simp only [List.length_nil, fixedLevelLaw]
      rw [Measure.pi_of_empty]
      rw [Measure.map_dirac' (measurable_fixedLevelFold [] initial)]
      rfl
  | cons step rest ih =>
      let law : Fin (rest.length + 1) → Measure (ι → Nat) :=
        fun i => fixedLevelIncomingLaw ((step :: rest).get i)
      have hprob (i : Fin (rest.length + 1)) : IsProbabilityMeasure (law i) :=
        fixedLevelIncomingLaw_isProbabilityMeasure _
      have hpi := pointCountVector_pi_fin_cons rest.length law hprob
      let head : Measure (ι → Nat) := fixedLevelIncomingLaw step
      let tail : Measure (Fin rest.length → ι → Nat) :=
        Measure.pi (fun i : Fin rest.length => fixedLevelIncomingLaw (rest.get i))
      let update : (ι → Nat) → (ι → Nat) := fun fresh x =>
        (if x ∈ step.deleted then 0 else initial x) + fresh x
      have hhead : law 0 = head := by simp [law, head]
      have htail : (Measure.pi (fun i : Fin rest.length => law i.succ)) =
          tail := by
        rfl
      have hpi' : (head.bind fun fresh => tail.map
          (fun future : Fin rest.length → ι → Nat =>
            (Fin.cons fresh future : Fin (rest.length + 1) → ι → Nat))) =
          Measure.pi law := by
        simpa only [hhead, htail] using hpi
      have htailKernel : Measurable (fun fresh : ι → Nat =>
          tail.map (fun future : Fin rest.length → ι → Nat =>
            (Fin.cons fresh future : Fin (rest.length + 1) → ι → Nat))) :=
        Measurable.of_discrete
      have hfold : Measurable (fixedLevelFold (step :: rest) initial) :=
        measurable_fixedLevelFold _ _
      have hfirst : (Measure.pi law).map
          (fixedLevelFold (step :: rest) initial) =
          head.bind (fun fresh =>
            tail.map (fixedLevelFold rest (update fresh))) := by
        rw [← hpi']
        rw [map_bind_measure head
          (fun fresh => tail.map
            (fun future : Fin rest.length → ι → Nat =>
              (Fin.cons fresh future : Fin (rest.length + 1) → ι → Nat)))
          (fixedLevelFold (step :: rest) initial)
          htailKernel.aemeasurable hfold]
        apply Measure.bind_congr_right
        apply Filter.Eventually.of_forall
        intro fresh
        dsimp only
        rw [Measure.map_map hfold (Measurable.of_discrete)]
        rfl
      have htailFold (fresh : ι → Nat) :
          tail.map (fixedLevelFold rest (update fresh)) =
            fixedLevelLaw rest (Measure.dirac (update fresh)) := ih _
      have hbase : ((Measure.dirac initial).prod head).map
          (fun pair : (ι → Nat) × (ι → Nat) =>
            fun x => (if x ∈ step.deleted then 0 else pair.1 x) + pair.2 x) =
          head.map update := by
        rw [Measure.prod_eq_bind_map]
        rw [Measure.dirac_bind (Measurable.of_discrete)]
        rw [Measure.map_map (Measurable.of_discrete) measurable_prodMk_left]
        rfl
      change (Measure.pi law).map (fixedLevelFold (step :: rest) initial) =
        fixedLevelLaw rest
          (((Measure.dirac initial).prod head).map
            (fun pair : (ι → Nat) × (ι → Nat) =>
              fun x => (if x ∈ step.deleted then 0 else pair.1 x) + pair.2 x))
      rw [hfirst, hbase]
      simp_rw [htailFold]
      rw [fixedLevelLaw_bind_initial rest (head.map update)]
      rw [bind_mapped_measure head update (Measurable.of_discrete)
        (fun state => fixedLevelLaw rest (Measure.dirac state))
        (Measurable.of_discrete)]

theorem fixedLevelFold_source_pi_eq_fixedLevelLaw
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α]
    (steps : List (FixedLevelStep ι)) (initial : ι → Nat)
    (sourceLaw : Fin steps.length → Measure α)
    (draw : Fin steps.length → α → ι → Nat)
    (hdrawMeas : ∀ i, Measurable (draw i))
    (hdrawLaw : ∀ i, (sourceLaw i).map (draw i) =
      fixedLevelIncomingLaw (steps.get i)) :
    (Measure.pi sourceLaw).map
      (fun sources => fixedLevelFold steps initial
        (fun i => draw i (sources i))) =
      fixedLevelLaw steps (Measure.dirac initial) := by
  let f : (Fin steps.length → α) → (Fin steps.length → ι → Nat) :=
    fun sources i => draw i (sources i)
  have hf : Measurable f :=
    Measurable.of_eval (fun i => (hdrawMeas i).comp (measurable_pi_apply i))
  have hmap (i : Fin steps.length) : IsProbabilityMeasure
      ((sourceLaw i).map (draw i)) := by
    rw [hdrawLaw i]
    exact fixedLevelIncomingLaw_isProbabilityMeasure _
  letI : ∀ i : Fin steps.length, SigmaFinite
      ((sourceLaw i).map (draw i)) := fun i => by
    letI := hmap i
    infer_instance
  calc
    (Measure.pi sourceLaw).map
        (fun sources => fixedLevelFold steps initial (f sources)) =
      ((Measure.pi sourceLaw).map f).map
        (fixedLevelFold steps initial) := by
          rw [Measure.map_map (measurable_fixedLevelFold steps initial) hf]
          rfl
    _ = (Measure.pi (fun i => (sourceLaw i).map (draw i))).map
          (fixedLevelFold steps initial) := by
            rw [Measure.pi_map_pi (fun i => (hdrawMeas i).aemeasurable)]
    _ = (Measure.pi (fun i : Fin steps.length =>
          fixedLevelIncomingLaw (steps.get i))).map
          (fixedLevelFold steps initial) := by simp_rw [hdrawLaw]
    _ = _ := fixedLevelFold_pi_eq_fixedLevelLaw steps initial

end Kr25Ssmxt
