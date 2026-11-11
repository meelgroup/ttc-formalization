import Kr25Ssmxt.Analysis.ManuscriptOriginGivenVolumesFold
import Kr25Ssmxt.Analysis.ManuscriptGivenVolumeFold
import Kr25Ssmxt.Analysis.ManuscriptOriginOrderedMarginal

/-! The given-volumes ghost fold projects to the executable given-volumes
fold, and starting it from the refreshed initial configuration changes
nothing. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

theorem ManuscriptOriginConfiguration.refreshLaw_refreshFuture
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) :
    (c.refreshFuture future).refreshLaw = c.refreshLaw := by
  unfold ManuscriptOriginConfiguration.refreshLaw
  congr 1
  funext second
  exact c.refreshFuture_twice future second

theorem manuscriptOriginRefreshedComponentLaw_refreshFuture
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n)
    (future : Nat × (Nat × Nat) → Bool) :
    manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
        intensity (c.refreshFuture future) =
      manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
        intensity c := by
  unfold manuscriptOriginRefreshedComponentLaw
  rw [c.refreshLaw_refreshFuture future]

/-- A nonempty ghost fold already begins by refreshing, so a leading
refresh is absorbed. -/
theorem manuscriptOriginGivenVolumesLaw_refreshLaw_bind
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (d : ManuscriptOriginCertifiedComponent n k hn prep b eta delta)
    (rest : List (ManuscriptOriginCertifiedComponent n k hn prep b eta delta))
    (outcomes : Fin (d :: rest).length → VolumeOutcome)
    (c : ManuscriptOriginConfiguration n) :
    c.refreshLaw.bind (manuscriptOriginGivenVolumesLaw hn prep b eta delta
        threshold (d :: rest) outcomes) =
      manuscriptOriginGivenVolumesLaw hn prep b eta delta threshold
        (d :: rest) outcomes c := by
  let sourceLaw : Measure (Nat × (Nat × Nat) → Bool) :=
    Measure.infinitePi (fun _ => fairCoinLaw)
  let _ : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  let _ : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  have hG := measurable_manuscriptOriginGivenVolumesLaw hn prep b eta delta
    threshold hthreshold (d :: rest) outcomes
  change (sourceLaw.map c.refreshFuture).bind _ = _
  rw [bind_mapped_measure sourceLaw c.refreshFuture c.measurable_refreshFuture
    _ hG]
  have hconst : (fun future => manuscriptOriginGivenVolumesLaw hn prep b eta
      delta threshold (d :: rest) outcomes (c.refreshFuture future)) =
      fun _ => manuscriptOriginGivenVolumesLaw hn prep b eta delta threshold
        (d :: rest) outcomes c := by
    funext future
    change (manuscriptOriginRefreshedComponentLaw hn d.polytope b eta
        threshold d.route _ (c.refreshFuture future)).bind _ =
      (manuscriptOriginRefreshedComponentLaw hn d.polytope b eta threshold
        d.route _ c).bind _
    rw [manuscriptOriginRefreshedComponentLaw_refreshFuture]
  rw [hconst, Measure.bind_const]
  simp

theorem poissonMeasure_zero_pi_eq_dirac {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    Measure.pi (fun _ : ι => ProbabilityTheory.poissonMeasure 0) =
      Measure.dirac (fun _ : ι => 0) := by
  have hzero : ProbabilityTheory.poissonMeasure 0 = Measure.dirac 0 := by
    apply Measure.ext_of_singleton
    intro k
    rw [ProbabilityTheory.poissonMeasure_singleton]
    by_cases hk : k = 0
    · subst hk
      simp
    · have hne : (0 : Nat) ≠ k := fun h => hk h.symm
      simp [hk, hne]
  rw [hzero]
  apply Measure.ext_of_singleton
  intro f
  rw [← Set.univ_pi_singleton, Measure.pi_pi, Set.univ_pi_singleton]
  by_cases h : ∀ i, f i = 0
  · have hf : f = fun _ => 0 := funext h
    subst hf
    simp
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi])]
    have hne : (fun _ : ι => (0 : Nat)) ≠ f := by
      intro heq
      exact hi (congrFun heq i).symm
    simp [hne]

/-- At every fixed level the refreshed initial configuration has no source
tags, hence zero point counts. -/
theorem manuscriptOrigin_initial_refreshLaw_pointCounts
    {n : Nat} (level : Nat) (S : Finset (LatticePoint n)) :
    (ManuscriptOriginConfiguration.initial n).refreshLaw.map
        (fun c : ManuscriptOriginConfiguration n =>
          c.source.pointCounts level S) =
      Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0) := by
  let _ : ∀ _ : Nat × (Nat × Nat), IsProbabilityMeasure fairCoinLaw :=
    fun _ => fairCoinLaw_isProbabilityMeasure
  rw [poissonMeasure_zero_pi_eq_dirac]
  have hcounts : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.source.pointCounts level S) :=
    (measurable_manuscriptOriginSourceState_pointCounts level S).comp
      measurable_manuscriptOriginConfiguration_source
  unfold ManuscriptOriginConfiguration.refreshLaw
  rw [Measure.map_map hcounts
    (ManuscriptOriginConfiguration.initial n).measurable_refreshFuture]
  have hfun : ((fun c : ManuscriptOriginConfiguration n =>
      c.source.pointCounts level S) ∘
        (ManuscriptOriginConfiguration.initial n).refreshFuture) =
      fun _ => fun _ : S => 0 := by
    funext future x
    simp [Function.comp_apply, ManuscriptOriginSourceState.pointCounts,
      manuscriptOriginSourcePointCounts,
      ManuscriptOriginConfiguration.refreshFuture,
      ManuscriptOriginConfiguration.initial,
      ManuscriptOriginSourceState.initial]
    rfl
  rw [hfun, Measure.map_const]
  simp

set_option maxHeartbeats 1000000 in
/-- The ghost fold at fixed outcomes projects to the executable fold at the
same outcomes. -/
theorem manuscriptOriginGivenVolumesLaw_map_state
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List
      (ManuscriptOriginCertifiedComponent n k hn prep b eta delta))
    (outcomes : Fin components.length → VolumeOutcome)
    (c : ManuscriptOriginConfiguration n) :
    (manuscriptOriginGivenVolumesLaw hn prep b eta delta threshold
      components outcomes c).map (fun next => next.state) =
    communityManuscriptComponentsGivenVolumes hn prep b eta delta threshold
      (components.map (fun d => d.polytope))
      (fun i => outcomes (Fin.cast (List.length_map _) i)) c.state := by
  induction components generalizing c with
  | nil =>
      change (Measure.dirac c).map _ = Measure.dirac c.state
      exact Measure.map_dirac' measurable_manuscriptOriginConfiguration_state c
  | cons d rest ih =>
      let intensity := ttcPseudocode.t b n threshold (outcomes 0).2
      let R := manuscriptOriginRefreshedComponentLaw hn d.polytope b eta
        threshold d.route intensity
      let G := manuscriptOriginGivenVolumesLaw hn prep b eta delta threshold
        rest (fun i => outcomes i.succ)
      let E := communityManuscriptComponentsGivenVolumes hn prep b eta delta
        threshold (rest.map (fun d => d.polytope))
        (fun i => outcomes (Fin.cast (List.length_map _) i).succ)
      have hG : Measurable G :=
        measurable_manuscriptOriginGivenVolumesLaw hn prep b eta delta
          threshold hthreshold rest (fun i => outcomes i.succ)
      have hE : Measurable E := by
        have h := (measurable_communityManuscriptComponentsGivenVolumes hn
          prep b eta delta threshold hthreshold
          (rest.map (fun d => d.polytope))).comp
          ((measurable_const (a := fun i : Fin (rest.map
            (fun d => d.polytope)).length =>
              outcomes (Fin.cast (List.length_map _) i).succ)).prodMk
            measurable_id)
        exact h
      have hstep : (R c).map (fun next => next.state) =
          communityManuscriptComponentGivenVolume hn prep d.polytope b eta
            delta threshold (outcomes 0) c.state :=
        manuscriptOriginRefreshedComponentLaw_map_state_eq_givenVolume hn
          prep d.polytope b eta delta threshold hthreshold d.route c
          (outcomes 0)
      calc
        (manuscriptOriginGivenVolumesLaw hn prep b eta delta threshold
            (d :: rest) outcomes c).map (fun next => next.state) =
            (R c).bind (fun next => (G next).map (fun x => x.state)) :=
          map_bind_measure (R c) G (fun x => x.state) hG.aemeasurable
            measurable_manuscriptOriginConfiguration_state
        _ = (R c).bind (fun next => E next.state) := by
          apply Measure.bind_congr_right
          apply Filter.Eventually.of_forall
          intro next
          exact ih (fun i => outcomes i.succ) next
        _ = ((R c).map (fun next => next.state)).bind E :=
          (bind_mapped_measure (R c) (fun next => next.state)
            measurable_manuscriptOriginConfiguration_state E hE).symm
        _ = _ := by
          rw [hstep]
          rfl

end Kr25Ssmxt
