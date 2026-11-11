import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.ComponentPredrawTape
import Kr25Ssmxt.Analysis.ComponentsVolumeTrace
import Kr25Ssmxt.Analysis.ProductBindSwap

/-! Condition the executable component fold on the independent CV18 volume
outcomes while retaining the complete sampling and thinning program. -/

namespace Kr25Ssmxt

open MeasureTheory

private theorem bind_independent_comm
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : α × β → Measure γ) (hK : Measurable K) :
    μ.bind (fun a => ν.bind fun b => K (a, b)) =
      ν.bind (fun b => μ.bind fun a => K (a, b)) := by
  have hleft : μ.bind (fun a => ν.bind fun b => K (a, b)) =
      (μ.prod ν).bind K := by
    rw [Measure.prod_eq_bind_map]
    rw [Measure.bind_bind Measurable.map_prodMk_left.aemeasurable
      hK.aemeasurable]
    congr 1
    funext a
    exact (bind_mapped_measure ν (Prod.mk a) measurable_prodMk_left
      K hK).symm
  have hright : ν.bind (fun b => μ.bind fun a => K (a, b)) =
      (ν.prod μ).bind (fun z => K z.swap) := by
    change _ = (ν.prod μ).bind (K ∘ Prod.swap)
    rw [Measure.prod_eq_bind_map]
    rw [Measure.bind_bind Measurable.map_prodMk_left.aemeasurable
      (hK.comp measurable_swap).aemeasurable]
    congr 1
    funext b
    exact (bind_mapped_measure μ (Prod.mk b) measurable_prodMk_left
      (fun z => K z.swap) (hK.comp measurable_swap)).symm
  exact hleft.trans ((measure_prod_bind_swap μ ν K hK).trans hright.symm)

theorem measurable_communityComponentGivenVolume
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold) :
    Measurable (fun z : TTCState n × VolumeOutcome =>
      communityComponentGivenVolume hn prep P b eta delta
        threshold z.2 z.1) := by
  let costed : TTCState n × VolumeOutcome →
      Measure (TTCState n × Nat) := fun z =>
    communityCostedComponentTail hn prep 1 P b eta delta threshold
      z.1 z.2
  have hcosted : Measurable costed :=
    community_component_tail_joint_measurable
      hn prep 1 P b eta delta threshold hthreshold
  have hmap : Measurable (fun z : TTCState n × VolumeOutcome =>
      (costed z).map Prod.fst) :=
    (Measure.measurable_map Prod.fst measurable_fst).comp hcosted
  convert hmap using 1
  funext z
  change communityComponentGivenVolume hn prep P b eta delta
      threshold z.2 z.1 = _
  unfold communityComponentGivenVolume
  exact (community_deletion_tail_fst hn prep 1 P b eta delta
    threshold hthreshold z.1
    (ttcPseudocode.t b n threshold z.2.2)).symm

theorem communityComponentGivenVolume_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (P : PolytopeData n) (b : Nat) (eta delta threshold : Real)
    (hthreshold : 0 < threshold) (outcome : VolumeOutcome)
    (state : TTCState n) :
    IsProbabilityMeasure
      (communityComponentGivenVolume hn prep P b eta delta
        threshold outcome state) := by
  have hmass := community_deletion_tail_mass_one
    hn prep 1 P b eta delta threshold hthreshold state
    (ttcPseudocode.t b n threshold outcome.2)
  have hmap : IsProbabilityMeasure
      ((communityCostedComponentTail hn prep 1 P b eta delta threshold
        state outcome).map Prod.fst) := by
    have hprob : IsProbabilityMeasure
        (communityCostedComponentTail hn prep 1 P b eta delta threshold
          state outcome) := ⟨hmass⟩
    letI := hprob
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  unfold communityComponentGivenVolume
  rw [← community_deletion_tail_fst hn prep 1 P b eta delta
    threshold hthreshold state
    (ttcPseudocode.t b n threshold outcome.2)]
  exact hmap

noncomputable def communityComponentsGivenVolumes
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) :
    (components : List (PolytopeData n)) →
    (outcomes : Fin components.length → VolumeOutcome) →
    TTCState n → Measure (TTCState n)
  | [], _, state => Measure.dirac state
  | P :: rest, outcomes, state =>
      (communityComponentGivenVolume hn prep P b eta delta
        threshold (outcomes 0) state).bind fun next =>
          communityComponentsGivenVolumes hn prep b eta delta
            threshold rest (fun i => outcomes i.succ) next

set_option maxHeartbeats 2000000 in
theorem measurable_communityComponentsGivenVolumes
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List (PolytopeData n)) :
    Measurable (fun z : (Fin components.length → VolumeOutcome) × TTCState n =>
      communityComponentsGivenVolumes hn prep b eta delta threshold
        components z.1 z.2) := by
  induction components with
  | nil =>
      exact Measure.measurable_dirac.comp measurable_snd
  | cons P rest ih =>
      let first : ((Fin (P :: rest).length → VolumeOutcome) × TTCState n) →
          Measure (TTCState n) := fun z =>
        communityComponentGivenVolume hn prep P b eta delta
          threshold (z.1 0) z.2
      have hfirst : Measurable first := by
        have hcoords : Measurable
            (fun z : (Fin (P :: rest).length → VolumeOutcome) × TTCState n =>
              (z.2, z.1 0)) :=
          measurable_snd.prodMk
            ((measurable_pi_apply 0).comp measurable_fst)
        have h := (measurable_communityComponentGivenVolume
          hn prep P b eta delta threshold hthreshold).comp hcoords
        exact h
      have hfirstProb (z : (Fin (P :: rest).length → VolumeOutcome) ×
          TTCState n) : IsProbabilityMeasure (first z) :=
        communityComponentGivenVolume_isProbabilityMeasure
          hn prep P b eta delta threshold hthreshold (z.1 0) z.2
      let next : (((Fin (P :: rest).length → VolumeOutcome) × TTCState n) ×
          TTCState n) → Measure (TTCState n) := fun z =>
        communityComponentsGivenVolumes hn prep b eta delta
          threshold rest (fun i => z.1.1 i.succ) z.2
      have htail : Measurable
          (fun z : Fin (P :: rest).length → VolumeOutcome =>
            (fun i : Fin rest.length => z i.succ)) :=
        Measurable.of_eval (fun i => measurable_pi_apply i.succ)
      have hnext : Measurable next := by
        exact ih.comp
          ((htail.comp (measurable_fst.comp measurable_fst)).prodMk
            measurable_snd)
      exact measurable_parametric_probability_bind first hfirst
        hfirstProb next hnext

set_option maxHeartbeats 2000000 in
theorem communityComponentsGivenVolumes_isProbabilityMeasure
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (outcomes : Fin components.length → VolumeOutcome)
    (state : TTCState n) :
    IsProbabilityMeasure
      (communityComponentsGivenVolumes hn prep b eta delta
        threshold components outcomes state) := by
  induction components generalizing state with
  | nil =>
      change IsProbabilityMeasure (Measure.dirac state)
      infer_instance
  | cons P rest ih =>
      let first := communityComponentGivenVolume hn prep P b eta
        delta threshold (outcomes 0) state
      let K : TTCState n → Measure (TTCState n) := fun next =>
        communityComponentsGivenVolumes hn prep b eta delta
          threshold rest (fun i => outcomes i.succ) next
      letI : IsProbabilityMeasure first :=
        communityComponentGivenVolume_isProbabilityMeasure
          hn prep P b eta delta threshold hthreshold (outcomes 0) state
      have hK : Measurable K := by
        exact (measurable_communityComponentsGivenVolumes
          hn prep b eta delta threshold hthreshold rest).comp
            (measurable_const.prodMk measurable_id)
      have hprob : ∀ next, IsProbabilityMeasure (K next) :=
        fun next => ih (fun i => outcomes i.succ) next
      change IsProbabilityMeasure (first.bind K)
      exact isProbabilityMeasure_bind hK.aemeasurable
        (Filter.Eventually.of_forall hprob)

theorem measurable_communityProcessComponents
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((ttcSubroutines hn prep).ComputeVolume P eta delta)) :
    Measurable (ttcPseudocode.loop
      (ttcSubroutines hn prep) b eta delta threshold components) := by
  induction components with
  | nil => exact Measure.measurable_dirac
  | cons P rest ih =>
      have hvolP : IsProbabilityMeasure
          ((ttcSubroutines hn prep).ComputeVolume P eta delta) :=
        hvolume P (by simp)
      have hvolRest : ∀ Q ∈ rest, IsProbabilityMeasure
          ((ttcSubroutines hn prep).ComputeVolume Q eta delta) := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      let first : TTCState n → Measure (TTCState n) := fun state =>
        ttcPseudocode.step (ttcSubroutines hn prep)
          b eta delta threshold P state
      have hfirst : Measurable first := by
        let volumeLaw := (ttcSubroutines hn prep).ComputeVolume
          P eta delta
        have hbase := measurable_parametric_probability_bind
          (fun _ : TTCState n => volumeLaw) measurable_const
          (fun _ => hvolP)
          (fun z : TTCState n × VolumeOutcome =>
            communityComponentGivenVolume hn prep P b eta delta
              threshold z.2 z.1)
          (measurable_communityComponentGivenVolume hn prep P b
            eta delta threshold hthreshold)
        change Measurable (fun state : TTCState n =>
          volumeLaw.bind fun outcome =>
            communityComponentGivenVolume hn prep P b eta delta
              threshold outcome state)
        exact hbase
      change Measurable (fun state => (first state).bind
        (ttcPseudocode.loop (ttcSubroutines hn prep)
          b eta delta threshold rest))
      exact (Measure.measurable_bind' (ih hvolRest)).comp hfirst

set_option maxHeartbeats 1200000 in
theorem communityProcessComponents_eq_volumeVector_bind
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List (PolytopeData n))
    (hvolume : ∀ P ∈ components, IsProbabilityMeasure
      ((ttcSubroutines hn prep).ComputeVolume P eta delta))
    (state : TTCState n) :
    ttcPseudocode.loop (ttcSubroutines hn prep)
      b eta delta threshold components state =
    (communityVolumeVectorLaw hn prep eta delta components).bind
      (fun outcomes =>
        communityComponentsGivenVolumes hn prep b eta delta
          threshold components outcomes state) := by
  induction components generalizing state with
  | nil =>
      simp [ttcPseudocode.loop, communityVolumeVectorLaw,
        communityComponentsGivenVolumes]
  | cons P rest ih =>
      have hvolP : IsProbabilityMeasure
          ((ttcSubroutines hn prep).ComputeVolume P eta delta) :=
        hvolume P (by simp)
      have hvolRest : ∀ Q ∈ rest, IsProbabilityMeasure
          ((ttcSubroutines hn prep).ComputeVolume Q eta delta) := by
        intro Q hQ
        exact hvolume Q (by simp [hQ])
      let μ := (ttcSubroutines hn prep).ComputeVolume P eta delta
      let ν := communityVolumeVectorLaw hn prep eta delta rest
      let G : VolumeOutcome → Measure (TTCState n) := fun outcome =>
        communityComponentGivenVolume hn prep P b eta delta
          threshold outcome state
      let R : (Fin rest.length → VolumeOutcome) → TTCState n →
          Measure (TTCState n) := fun outcomes next =>
        communityComponentsGivenVolumes hn prep b eta delta
          threshold rest outcomes next
      letI : IsProbabilityMeasure μ := hvolP
      letI : IsProbabilityMeasure ν :=
        communityVolumeVectorLaw_isProbabilityMeasure
          hn prep eta delta rest hvolRest
      have hG : Measurable G := by
        have hcoords : Measurable
            (fun outcome : VolumeOutcome => (state, outcome)) :=
          measurable_const.prodMk measurable_id
        have h := (measurable_communityComponentGivenVolume
          hn prep P b eta delta threshold hthreshold).comp hcoords
        exact h
      have hR : Measurable
          (fun z : (Fin rest.length → VolumeOutcome) × TTCState n =>
            R z.1 z.2) :=
        measurable_communityComponentsGivenVolumes
          hn prep b eta delta threshold hthreshold rest
      have hK : Measurable
          (fun z : TTCState n × (Fin rest.length → VolumeOutcome) =>
            R z.2 z.1) := hR.comp measurable_swap
      have htail : Measurable
          (ttcPseudocode.loop (ttcSubroutines hn prep)
            b eta delta threshold rest) :=
        measurable_communityProcessComponents
          hn prep b eta delta threshold hthreshold rest hvolRest
      let H : (Fin (P :: rest).length → VolumeOutcome) →
          Measure (TTCState n) := fun outcomes =>
        communityComponentsGivenVolumes hn prep b eta delta
          threshold (P :: rest) outcomes state
      have hH : Measurable H := by
        have hcoords : Measurable
            (fun outcomes : Fin (P :: rest).length → VolumeOutcome =>
              (outcomes, state)) := measurable_id.prodMk measurable_const
        have h := (measurable_communityComponentsGivenVolumes
          hn prep b eta delta threshold hthreshold (P :: rest)).comp
            hcoords
        exact h
      calc
        ttcPseudocode.loop (ttcSubroutines hn prep)
            b eta delta threshold (P :: rest) state =
          μ.bind (fun outcome => (G outcome).bind
            (ttcPseudocode.loop
              (ttcSubroutines hn prep)
              b eta delta threshold rest)) := by
                change (μ.bind G).bind _ = _
                exact Measure.bind_bind hG.aemeasurable htail.aemeasurable
        _ = μ.bind (fun outcome => (G outcome).bind
            (fun next => ν.bind fun outcomes => R outcomes next)) := by
              apply Measure.bind_congr_right
              apply Filter.Eventually.of_forall
              intro outcome
              apply Measure.bind_congr_right
              apply Filter.Eventually.of_forall
              intro next
              exact ih hvolRest next
        _ = μ.bind (fun outcome => ν.bind fun outcomes =>
            (G outcome).bind fun next => R outcomes next) := by
              apply Measure.bind_congr_right
              apply Filter.Eventually.of_forall
              intro outcome
              letI : IsProbabilityMeasure (G outcome) :=
                communityComponentGivenVolume_isProbabilityMeasure
                  hn prep P b eta delta threshold hthreshold outcome state
              exact bind_independent_comm (G outcome) ν
                (fun z => R z.2 z.1) hK
        _ = (communityVolumeVectorLaw hn prep eta delta
            (P :: rest)).bind H := by
              let cons : VolumeOutcome →
                  (Fin rest.length → VolumeOutcome) →
                  (Fin (rest.length + 1) → VolumeOutcome) :=
                fun outcome vec => Fin.cons outcome vec
              change _ = (μ.bind (fun outcome =>
                ν.map (cons outcome))).bind H
              have hcons : Measurable
                  (fun z : VolumeOutcome ×
                    (Fin rest.length → VolumeOutcome) =>
                    cons z.1 z.2) :=
                measurable_finCons_volumeOutcome rest.length
              have hmapFamily : Measurable
                  (fun outcome : VolumeOutcome =>
                    ν.map (cons outcome)) := by
                have hleft : Measurable
                    (fun outcome : VolumeOutcome =>
                      ν.map (Prod.mk outcome)) :=
                  Measurable.map_prodMk_left
                have hright := (Measure.measurable_map _ hcons).comp hleft
                convert hright using 1
                funext outcome
                change ν.map (cons outcome) =
                  (ν.map (Prod.mk outcome)).map
                    (fun z => cons z.1 z.2)
                rw [Measure.map_map hcons measurable_prodMk_left]
                rfl
              rw [Measure.bind_bind hmapFamily.aemeasurable
                hH.aemeasurable]
              congr 1
              funext outcome
              rw [bind_mapped_measure ν (cons outcome)
                (hcons.comp (measurable_const.prodMk measurable_id)) H hH]
              rfl

end Kr25Ssmxt
