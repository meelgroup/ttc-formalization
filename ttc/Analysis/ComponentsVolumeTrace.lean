import ttc.Analysis.MathlibCompat
import ttc.Analysis.ComponentVolumeTrace

/-! Record CV18 outcomes while executing the charged paper component
list, keeping the original total operation count in the second coordinate. -/

namespace ttc

open MeasureTheory

theorem measurable_finCons_volumeOutcome (m : Nat) :
    Measurable (fun pair : VolumeOutcome × (Fin m → VolumeOutcome) =>
      (Fin.cons pair.1 pair.2 : Fin (m + 1) → VolumeOutcome)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa only [Fin.cons_zero] using
      (measurable_fst : Measurable
        (fun pair : VolumeOutcome × (Fin m → VolumeOutcome) => pair.1))
  · intro j
    simpa only [Fin.cons_succ, Function.comp_def] using
      (measurable_pi_apply j).comp
        (measurable_snd : Measurable
          (fun pair : VolumeOutcome × (Fin m → VolumeOutcome) => pair.2))

def traceJoin {n : Nat} (m : Nat)
    (z : ((VolumeOutcome × Nat) × (TTCState n × Nat)) ×
      ((Fin m → VolumeOutcome) × (TTCState n × Nat))) :
    (Fin (m + 1) → VolumeOutcome) × (TTCState n × Nat) :=
  (Fin.cons z.1.1.1 z.2.1,
    (z.2.2.1, z.1.2.2 + z.2.2.2))

theorem measurable_traceJoin {n : Nat} (m : Nat) :
    Measurable (traceJoin (n := n) m) := by
  have hpair : Measurable
      (fun z : ((VolumeOutcome × Nat) × (TTCState n × Nat)) ×
        ((Fin m → VolumeOutcome) × (TTCState n × Nat)) =>
          (z.1.1.1, z.2.1)) := by fun_prop
  have hhead := (measurable_finCons_volumeOutcome m).comp hpair
  have hstate : Measurable
      (fun z : ((VolumeOutcome × Nat) × (TTCState n × Nat)) ×
        ((Fin m → VolumeOutcome) × (TTCState n × Nat)) => z.2.2.1) := by
    fun_prop
  have hcost : Measurable
      (fun z : ((VolumeOutcome × Nat) × (TTCState n × Nat)) ×
        ((Fin m → VolumeOutcome) × (TTCState n × Nat)) =>
          z.1.2.2 + z.2.2.2) := by fun_prop
  exact hhead.prodMk (hstate.prodMk hcost)

/-- The first coordinate and the remaining finite product coordinates form
the ordinary product law when assembled with `Fin.cons`. -/
theorem volumeOutcome_pi_fin_cons (m : Nat)
    (law : Fin (m + 1) → Measure VolumeOutcome)
    (hprob : ∀ i, IsProbabilityMeasure (law i)) :
    (law 0).bind (fun outcome =>
      (Measure.pi (fun i : Fin m => law i.succ)).map
        (fun vec : Fin m → VolumeOutcome =>
          (Fin.cons outcome vec : Fin (m + 1) → VolumeOutcome))) =
    Measure.pi law := by
  letI : ∀ i, IsProbabilityMeasure (law i) := hprob
  let tail : Measure (Fin m → VolumeOutcome) :=
    Measure.pi (fun i : Fin m => law i.succ)
  letI : IsProbabilityMeasure tail := inferInstance
  have hcons : Measurable
      (fun pair : VolumeOutcome × (Fin m → VolumeOutcome) =>
        (Fin.cons pair.1 pair.2 : Fin (m + 1) → VolumeOutcome)) :=
    measurable_finCons_volumeOutcome m
  have hproduct : ((law 0).prod tail).map
      (fun pair : VolumeOutcome × (Fin m → VolumeOutcome) =>
        (Fin.cons pair.1 pair.2 : Fin (m + 1) → VolumeOutcome)) =
      (law 0).bind (fun outcome => tail.map
        (fun vec : Fin m → VolumeOutcome =>
          (Fin.cons outcome vec : Fin (m + 1) → VolumeOutcome))) := by
    rw [Measure.prod_eq_bind_map]
    rw [map_bind_measure (law 0)
      (fun outcome => tail.map (Prod.mk outcome))
      (fun pair : VolumeOutcome × (Fin m → VolumeOutcome) =>
        (Fin.cons pair.1 pair.2 : Fin (m + 1) → VolumeOutcome))
      Measurable.map_prodMk_left.aemeasurable hcons]
    congr 1
    funext outcome
    rw [Measure.map_map hcons measurable_prodMk_left]
    rfl
  rw [← hproduct]
  apply (Measure.pi_eq (μ := law) (μ' :=
    ((law 0).prod tail).map
      (fun pair : VolumeOutcome × (Fin m → VolumeOutcome) =>
        (Fin.cons pair.1 pair.2 : Fin (m + 1) → VolumeOutcome))) ?_).symm
  intro sets hsets
  have hpre : (fun pair : VolumeOutcome × (Fin m → VolumeOutcome) =>
      Fin.cons pair.1 pair.2) ⁻¹' Set.pi Set.univ sets =
      (sets 0) ×ˢ Set.pi Set.univ (fun i : Fin m => sets i.succ) := by
    ext pair
    simp [Set.mem_pi, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  rw [Measure.map_apply hcons (MeasurableSet.univ_pi hsets), hpre]
  rw [Measure.prod_prod (sets 0)
    (Set.pi Set.univ (fun i : Fin m => sets i.succ))]
  rw [Measure.pi_pi]
  rw [Fin.prod_univ_succ]

noncomputable def communityComponentsVolumeTrace
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold : Real) :
    (components : List (PolytopeData n)) → TTCState n →
      Measure ((Fin components.length → VolumeOutcome) × (TTCState n × Nat))
  | [], state => Measure.dirac (Fin.elim0, (state, 0))
  | P :: rest, state =>
      (communityComponentVolumeTrace hn prep factor P b eta delta
        threshold state).bind fun current =>
        (communityComponentsVolumeTrace hn prep factor b eta delta
          threshold rest current.2.1).map fun future =>
          traceJoin rest.length (current, future)

/-- The independent CV18 outcomes in component order. -/
noncomputable def communityVolumeVectorLaw
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (eta delta : Real) :
    (components : List (PolytopeData n)) →
      Measure (Fin components.length → VolumeOutcome)
  | [] => Measure.dirac Fin.elim0
  | P :: rest =>
      ((ttcSubroutines hn prep).ComputeVolume P eta delta).bind
        fun outcome =>
          (communityVolumeVectorLaw hn prep eta delta rest).map
            (Fin.cons outcome)

set_option maxHeartbeats 500000 in
theorem communityVolumeVectorLaw_isProbabilityMeasure
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (eta delta : Real) (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components,
      IsProbabilityMeasure
        ((ttcSubroutines hn prep).ComputeVolume P eta delta)) :
    IsProbabilityMeasure
      (communityVolumeVectorLaw hn prep eta delta components) := by
  induction components with
  | nil =>
      change IsProbabilityMeasure (Measure.dirac Fin.elim0)
      infer_instance
  | cons P rest ih =>
      letI : IsProbabilityMeasure
          ((ttcSubroutines hn prep).ComputeVolume P eta delta) :=
        hvolume P (by simp)
      have hrest : ∀ Q ∈ rest,
          IsProbabilityMeasure
            ((ttcSubroutines hn prep).ComputeVolume Q eta delta) := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      letI : IsProbabilityMeasure
          (communityVolumeVectorLaw hn prep eta delta rest) :=
        ih hrest
      let K : VolumeOutcome → Measure (Fin (P :: rest).length → VolumeOutcome) :=
        fun outcome =>
          (communityVolumeVectorLaw hn prep eta delta rest).map
            (Fin.cons outcome)
      have hK : Measurable K :=
        measurable_parametric_probability_map
          (fun _ : VolumeOutcome =>
            communityVolumeVectorLaw hn prep eta delta rest)
          measurable_const (fun _ => inferInstance)
          (fun z : VolumeOutcome × (Fin rest.length → VolumeOutcome) =>
            (Fin.cons z.1 z.2 :
              Fin (rest.length + 1) → VolumeOutcome))
          (measurable_finCons_volumeOutcome rest.length)
      have hKprob (outcome : VolumeOutcome) : IsProbabilityMeasure (K outcome) :=
        Measure.isProbabilityMeasure_map
          ((measurable_finCons_volumeOutcome rest.length).comp
            (measurable_const.prodMk measurable_id)).aemeasurable
      have hbind : IsProbabilityMeasure
          (((ttcSubroutines hn prep).ComputeVolume P eta delta).bind K) :=
        isProbabilityMeasure_bind hK.aemeasurable
          (Filter.Eventually.of_forall hKprob)
      simpa only [communityVolumeVectorLaw, K] using hbind

theorem communityVolumeVectorLaw_eq_pi
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (eta delta : Real) (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components,
      IsProbabilityMeasure
        ((ttcSubroutines hn prep).ComputeVolume P eta delta)) :
    communityVolumeVectorLaw hn prep eta delta components =
      Measure.pi (fun i : Fin components.length =>
        (ttcSubroutines hn prep).ComputeVolume
          (components.get i) eta delta) := by
  induction components with
  | nil =>
      rw [communityVolumeVectorLaw]
      exact (Measure.pi_of_empty _).symm
  | cons P rest ih =>
      have hrest : ∀ Q ∈ rest,
          IsProbabilityMeasure
            ((ttcSubroutines hn prep).ComputeVolume Q eta delta) := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      let law : Fin (rest.length + 1) → Measure VolumeOutcome :=
        fun i => (ttcSubroutines hn prep).ComputeVolume
          ((P :: rest).get i) eta delta
      have hprob (i : Fin (rest.length + 1)) :
          IsProbabilityMeasure (law i) := by
        exact hvolume ((P :: rest).get i) (List.get_mem _ _)
      have hpi := volumeOutcome_pi_fin_cons rest.length law hprob
      rw [communityVolumeVectorLaw, ih hrest]
      simpa [law] using hpi

set_option maxHeartbeats 1200000 in
theorem communityComponentsVolumeTrace_measurable_probability
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta)) :
    Measurable (communityComponentsVolumeTrace hn prep factor b
      eta delta threshold components) ∧
    ∀ state, IsProbabilityMeasure
      (communityComponentsVolumeTrace hn prep factor b
        eta delta threshold components state) := by
  induction components with
  | nil =>
      constructor
      · change Measurable (fun state : TTCState n =>
          Measure.dirac (Fin.elim0, (state, 0)))
        exact Measure.measurable_dirac.comp (by fun_prop)
      · intro state
        change IsProbabilityMeasure (Measure.dirac (Fin.elim0, (state, 0)))
        infer_instance
  | cons P rest ih =>
      have hvolP : IsProbabilityMeasure
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            P eta delta) := hvolume P (by simp)
      have hvolRest : ∀ Q ∈ rest, IsProbabilityMeasure
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            Q eta delta) := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      obtain ⟨hrestMeas, hrestProb⟩ := ih hvolRest
      let first : TTCState n →
          Measure ((VolumeOutcome × Nat) × (TTCState n × Nat)) :=
        communityComponentVolumeTrace hn prep factor P b eta delta
          threshold
      have hfirst : Measurable first :=
        communityComponentVolumeTrace_measurable hn prep factor P b
          eta delta threshold hthreshold hvolP
      have hfirstProb (state : TTCState n) : IsProbabilityMeasure (first state) :=
        communityComponentVolumeTrace_isProbabilityMeasure hn prep
          factor P b eta delta threshold hthreshold state hvolP
      let tail : (TTCState n ×
          ((VolumeOutcome × Nat) × (TTCState n × Nat))) →
          Measure ((Fin rest.length → VolumeOutcome) × (TTCState n × Nat)) :=
        fun z => communityComponentsVolumeTrace hn prep factor b
          eta delta threshold rest z.2.2.1
      have htail : Measurable tail :=
        hrestMeas.comp (by fun_prop)
      have htailProb (z : TTCState n ×
          ((VolumeOutcome × Nat) × (TTCState n × Nat))) :
          IsProbabilityMeasure (tail z) := hrestProb z.2.2.1
      let join : ((TTCState n ×
          ((VolumeOutcome × Nat) × (TTCState n × Nat))) ×
          ((Fin rest.length → VolumeOutcome) × (TTCState n × Nat))) →
          ((Fin (P :: rest).length → VolumeOutcome) × (TTCState n × Nat)) :=
        fun z => traceJoin rest.length (z.1.2, z.2)
      have hjoin : Measurable join := by
        exact (measurable_traceJoin rest.length).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
      let next : (TTCState n ×
          ((VolumeOutcome × Nat) × (TTCState n × Nat))) →
          Measure ((Fin (P :: rest).length → VolumeOutcome) ×
            (TTCState n × Nat)) :=
        fun z => (tail z).map fun future => join (z, future)
      have hnext : Measurable next :=
        measurable_parametric_probability_map tail htail htailProb join hjoin
      have hmeas : Measurable (fun state =>
          (first state).bind fun current => next (state, current)) :=
        measurable_parametric_probability_bind first hfirst hfirstProb next hnext
      constructor
      · change Measurable (fun state =>
          (first state).bind fun current => next (state, current))
        exact hmeas
      · intro state
        change IsProbabilityMeasure
          ((first state).bind fun current => next (state, current))
        letI : IsProbabilityMeasure (first state) := hfirstProb state
        apply isProbabilityMeasure_bind
          (hnext.comp (measurable_const.prodMk measurable_id)).aemeasurable
        filter_upwards with current
        letI : IsProbabilityMeasure (tail (state, current)) :=
          htailProb (state, current)
        exact Measure.isProbabilityMeasure_map
          ((hjoin.comp (measurable_const.prodMk measurable_id)).aemeasurable)

theorem community_trace_tail_measurable
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold : Real)
    (rest : List (PolytopeData n))
    (hrestMeas : Measurable
      (communityComponentsVolumeTrace hn prep factor b eta delta
        threshold rest))
    (hrestProb : ∀ state, IsProbabilityMeasure
      (communityComponentsVolumeTrace hn prep factor b eta delta
        threshold rest state)) :
    Measurable (fun current : (VolumeOutcome × Nat) × (TTCState n × Nat) =>
      (communityComponentsVolumeTrace hn prep factor b eta delta
        threshold rest current.2.1).map fun future =>
          traceJoin rest.length (current, future)) := by
  let tail : ((VolumeOutcome × Nat) × (TTCState n × Nat)) →
      Measure ((Fin rest.length → VolumeOutcome) × (TTCState n × Nat)) :=
    fun current => communityComponentsVolumeTrace hn prep factor b
      eta delta threshold rest current.2.1
  have htail : Measurable tail := hrestMeas.comp (by fun_prop)
  have hprob (current : (VolumeOutcome × Nat) × (TTCState n × Nat)) :
      IsProbabilityMeasure (tail current) := hrestProb current.2.1
  exact measurable_parametric_probability_map tail htail hprob
    (traceJoin rest.length)
    (measurable_traceJoin rest.length)

set_option maxHeartbeats 1200000 in
theorem communityComponentsVolumeTrace_volume_marginal
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta))
    (state : TTCState n) :
    (communityComponentsVolumeTrace hn prep factor b eta delta
      threshold components state).map Prod.fst =
    communityVolumeVectorLaw hn prep eta delta components := by
  induction components generalizing state with
  | nil =>
      simp [communityComponentsVolumeTrace,
        communityVolumeVectorLaw]
  | cons P rest ih =>
      have hvolP : IsProbabilityMeasure
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            P eta delta) := hvolume P (by simp)
      have hvolRest : ∀ Q ∈ rest, IsProbabilityMeasure
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            Q eta delta) := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      have hrest := communityComponentsVolumeTrace_measurable_probability
        hn prep factor b eta delta threshold hthreshold rest hvolRest
      let current : Measure ((VolumeOutcome × Nat) × (TTCState n × Nat)) :=
        communityComponentVolumeTrace hn prep factor P b eta delta
          threshold state
      let G : ((VolumeOutcome × Nat) × (TTCState n × Nat)) →
          Measure ((Fin (P :: rest).length → VolumeOutcome) ×
            (TTCState n × Nat)) := fun c =>
        (communityComponentsVolumeTrace hn prep factor b eta delta
          threshold rest c.2.1).map fun future =>
            traceJoin rest.length (c, future)
      have hG : Measurable G :=
        community_trace_tail_measurable hn prep factor b eta delta
          threshold rest hrest.1 hrest.2
      let vectorRest := communityVolumeVectorLaw hn prep eta delta rest
      have hvolRestBase : ∀ Q ∈ rest, IsProbabilityMeasure
          ((ttcSubroutines hn prep).ComputeVolume Q eta delta) := by
        intro Q hQ
        letI : IsProbabilityMeasure
            ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
              Q eta delta) := hvolRest Q hQ
        rw [← communityCosted_volume_fst hn prep factor Q eta delta]
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
      letI : IsProbabilityMeasure vectorRest :=
        communityVolumeVectorLaw_isProbabilityMeasure hn prep
          eta delta rest hvolRestBase
      let K : VolumeOutcome → Measure (Fin (P :: rest).length → VolumeOutcome) :=
        fun outcome => vectorRest.map (Fin.cons outcome)
      have hK : Measurable K :=
        measurable_parametric_probability_map
          (fun _ : VolumeOutcome => vectorRest) measurable_const
          (fun _ => inferInstance)
          (fun z : VolumeOutcome × (Fin rest.length → VolumeOutcome) =>
            (Fin.cons z.1 z.2 : Fin (rest.length + 1) → VolumeOutcome))
          (measurable_finCons_volumeOutcome rest.length)
      have hpoint (c : (VolumeOutcome × Nat) × (TTCState n × Nat)) :
          (G c).map Prod.fst = K c.1.1 := by
        let tail := communityComponentsVolumeTrace hn prep factor b
          eta delta threshold rest c.2.1
        have hjoin : Measurable (fun future :
            (Fin rest.length → VolumeOutcome) × (TTCState n × Nat) =>
              traceJoin rest.length (c, future)) :=
          (measurable_traceJoin rest.length).comp
            (measurable_const.prodMk measurable_id)
        calc
          (G c).map Prod.fst =
              tail.map (fun future => Fin.cons c.1.1 future.1) := by
            change ((tail.map (fun future =>
              traceJoin rest.length (c, future))).map Prod.fst) = _
            rw [Measure.map_map measurable_fst hjoin]
            rfl
          _ = (tail.map Prod.fst).map (Fin.cons c.1.1) := by
            have hcons : Measurable
                (fun v : Fin rest.length → VolumeOutcome =>
                  (Fin.cons c.1.1 v :
                    Fin (rest.length + 1) → VolumeOutcome)) := by
              simpa only [Function.comp_def, id_eq] using
                (measurable_finCons_volumeOutcome rest.length).comp
                  (measurable_const.prodMk measurable_id)
            rw [Measure.map_map hcons measurable_fst]
            rfl
          _ = K c.1.1 := by rw [ih hvolRest c.2.1]
      have hcurrent : current.map (fun c => c.1.1) =
          (ttcSubroutines hn prep).ComputeVolume P eta delta :=
        communityComponentVolumeTrace_volumeOutcome hn prep factor
          P b eta delta threshold hthreshold state
      change (current.bind G).map Prod.fst =
        ((ttcSubroutines hn prep).ComputeVolume P eta delta).bind K
      rw [map_bind_measure current G Prod.fst hG.aemeasurable measurable_fst]
      simp_rw [hpoint]
      rw [← bind_mapped_measure current (fun c => c.1.1) (by fun_prop) K hK]
      rw [hcurrent]

/-- The complete charged paper trace has the independent product of
its concrete CV18 outcome laws as its volume marginal. -/
theorem communityComponentsVolumeTrace_volume_pi
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta))
    (state : TTCState n) :
    (communityComponentsVolumeTrace hn prep factor b eta delta
      threshold components state).map Prod.fst =
      Measure.pi (fun i : Fin components.length =>
        (ttcSubroutines hn prep).ComputeVolume
          (components.get i) eta delta) := by
  rw [communityComponentsVolumeTrace_volume_marginal hn prep factor
    b eta delta threshold hthreshold components hvolume state]
  apply communityVolumeVectorLaw_eq_pi
  intro P hP
  letI : IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta) := hvolume P hP
  rw [← communityCosted_volume_fst hn prep factor P eta delta]
  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

set_option maxHeartbeats 1200000 in
theorem communityComponentsVolumeTrace_run_marginal
    {n k : Nat} (hn : 3 ≤ n) (prep : TTCPreprocessor n k)
    (factor b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
        P eta delta))
    (state : TTCState n) :
    (communityComponentsVolumeTrace hn prep factor b eta delta
      threshold components state).map Prod.snd =
    ttcReference.loopWithCost
      (ttcCostedSubroutines hn prep factor)
      b eta delta threshold components state := by
  induction components generalizing state with
  | nil =>
      simp [communityComponentsVolumeTrace,
        ttcReference.loopWithCost]
  | cons P rest ih =>
      have hvolP : IsProbabilityMeasure
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            P eta delta) := hvolume P (by simp)
      have hvolRest : ∀ Q ∈ rest, IsProbabilityMeasure
          ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
            Q eta delta) := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      have hrest := communityComponentsVolumeTrace_measurable_probability
        hn prep factor b eta delta threshold hthreshold rest hvolRest
      let current : Measure ((VolumeOutcome × Nat) × (TTCState n × Nat)) :=
        communityComponentVolumeTrace hn prep factor P b eta delta
          threshold state
      let G : ((VolumeOutcome × Nat) × (TTCState n × Nat)) →
          Measure ((Fin (P :: rest).length → VolumeOutcome) ×
            (TTCState n × Nat)) := fun c =>
        (communityComponentsVolumeTrace hn prep factor b eta delta
          threshold rest c.2.1).map fun future =>
            traceJoin rest.length (c, future)
      have hG : Measurable G :=
        community_trace_tail_measurable hn prep factor b eta delta
          threshold rest hrest.1 hrest.2
      let K : (TTCState n × Nat) → Measure (TTCState n × Nat) :=
        fun c => (ttcReference.loopWithCost
          (ttcCostedSubroutines hn prep factor)
          b eta delta threshold rest c.1).map fun future =>
            (future.1, c.2 + future.2)
      have htailMeas : Measurable (fun s : TTCState n =>
          ttcReference.loopWithCost
            (ttcCostedSubroutines hn prep factor)
            b eta delta threshold rest s) := by
        apply community_components_kernel_measurable hn prep factor
          b eta delta threshold hthreshold rest
        intro Q hQ
        letI : IsProbabilityMeasure
            ((ttcCostedSubroutines hn prep factor).computeVolumeWithCost
              Q eta delta) := hvolRest Q hQ
        simp
      have hK : Measurable K :=
        measurable_costedTrace_tail _ htailMeas
      have hpoint (c : (VolumeOutcome × Nat) × (TTCState n × Nat)) :
          (G c).map Prod.snd = K c.2 := by
        let tail := communityComponentsVolumeTrace hn prep factor b
          eta delta threshold rest c.2.1
        have hjoin : Measurable (fun future :
            (Fin rest.length → VolumeOutcome) × (TTCState n × Nat) =>
              traceJoin rest.length (c, future)) :=
          (measurable_traceJoin rest.length).comp
            (measurable_const.prodMk measurable_id)
        calc
          (G c).map Prod.snd =
              tail.map (fun future =>
                (future.2.1, c.2.2 + future.2.2)) := by
            change ((tail.map (fun future =>
              traceJoin rest.length (c, future))).map Prod.snd) = _
            rw [Measure.map_map measurable_snd hjoin]
            rfl
          _ = (tail.map Prod.snd).map
              (fun future => (future.1, c.2.2 + future.2)) := by
            rw [Measure.map_map (by fun_prop) measurable_snd]
            rfl
          _ = K c.2 := by rw [ih hvolRest c.2.1]
      have hcurrent : current.map Prod.snd =
          ttcReference.stepWithCost
            (ttcCostedSubroutines hn prep factor)
            b eta delta threshold P state :=
        communityComponentVolumeTrace_snd hn prep factor P b
          eta delta threshold hthreshold state
      change (current.bind G).map Prod.snd =
        costedBind
          (ttcReference.stepWithCost
            (ttcCostedSubroutines hn prep factor)
            b eta delta threshold P state)
          (ttcReference.loopWithCost
            (ttcCostedSubroutines hn prep factor)
            b eta delta threshold rest)
      rw [map_bind_measure current G Prod.snd hG.aemeasurable measurable_snd]
      simp_rw [hpoint]
      rw [← bind_mapped_measure current Prod.snd measurable_snd K hK]
      rw [hcurrent]
      rfl

end ttc
