import Kr25Ssmxt.Analysis.MeasurablePoissonThinTail
import Kr25Ssmxt.Analysis.MeasurableRemoveComponent
import Kr25Ssmxt.Analysis.MeasurableVolumePoissonWeight

/-!
# Volume-oracle bind for one component iteration

This module isolates the outermost, state-parameterized bind against the fixed
volume-oracle measure in `processComponent`.
-/

namespace Kr25Ssmxt

/--
Binding the volume-oracle output to the measurable Poisson/thinning/sampling
continuation gives a measurable kernel in the incoming state.

INTERNAL: outer parameterized oracle bind in the `processComponent` assembly.
-/
lemma measurable_volume_process_tail {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n)
    (hpoisson : Measurable
      (fun r : NNReal => ProbabilityTheory.poissonMeasure r))
    (hremove : Measurable (fun state : TTCState n => state.removeComponent P))
    (hadd : ∀ count, Measurable
      (fun z : TTCState n × (Fin count → LatticePoint n) => z.1.addBatch z.2))
    (hthin : Measurable
      (fun z : TTCState n × Nat => thinUntil z.1 z.2 threshold)) :
    Measurable (fun state : TTCState n =>
      (O.computeVolume P epsilonPrime deltaPrime).bind fun volumeOutcome =>
        let withoutDuplicates := state.removeComponent P
        (ProbabilityTheory.poissonMeasure
          (volumeOutcome.2 / withoutDuplicates.rate)).bind fun pending =>
          (thinUntil withoutDuplicates pending threshold).bind fun thinned =>
            (O.generateSamples P thinned.2 b epsilonPrime deltaPrime).bind fun batch =>
              (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst) := by
  have htail := measurable_poisson_thin_tail O b epsilonPrime deltaPrime threshold P
    hpoisson hadd hthin
  have hafter := measurable_thin_sample_add O b epsilonPrime deltaPrime threshold P
    hadd hthin
  let mu : MeasureTheory.Measure VolumeOutcome :=
    O.computeVolume P epsilonPrime deltaPrime
  let R : TTCState n → TTCState n := fun state => state.removeComponent P
  let H : TTCState n × Nat → MeasureTheory.Measure (TTCState n) := fun z =>
    (thinUntil z.1 z.2 threshold).bind fun thinned =>
      (O.generateSamples P thinned.2 b epsilonPrime deltaPrime).bind fun batch =>
        (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst
  let K : TTCState n × VolumeOutcome → MeasureTheory.Measure (TTCState n) := fun z =>
    (ProbabilityTheory.poissonMeasure (z.2.2 / z.1.rate)).bind fun pending =>
      H (z.1, pending)
  have hR : Measurable R := by
    simpa only [R] using hremove
  have hH : Measurable H := by
    simpa only [H] using hafter
  have hK : Measurable K := by
    simpa only [K, H] using htail
  have hrateState : Measurable (fun state : TTCState n => state.rate) :=
    measurable_fst.comp
      (comap_measurable (fun state : TTCState n =>
        (state.rate, state.samples, state.nextLabel)))
  have hrate : Measurable (fun state : TTCState n => (R state).rate) :=
    hrateState.comp hR
  change Measurable (fun state : TTCState n => mu.bind fun volumeOutcome =>
    K (R state, volumeOutcome))
  refine MeasureTheory.Measure.measurable_of_measurable_coe _ ?_
  intro event hevent
  have hKsection : ∀ state : TTCState n,
      Measurable (fun volumeOutcome : VolumeOutcome => K (R state, volumeOutcome)) := by
    intro state
    exact hK.comp (measurable_const.prodMk measurable_id)
  simp_rw [MeasureTheory.Measure.bind_apply hevent (hKsection _).aemeasurable]
  have hexpand : ∀ state : TTCState n,
      (∫⁻ volumeOutcome, K (R state, volumeOutcome) event ∂mu) =
        ∑' pending : Nat,
          H (R state, pending) event *
            ∫⁻ volumeOutcome,
              (ProbabilityTheory.poissonMeasure
                (volumeOutcome.2 / (R state).rate)) {pending} ∂mu := by
    intro state
    have hHsection : Measurable (fun pending : Nat => H (R state, pending)) :=
      hH.comp (measurable_const.prodMk measurable_id)
    have hlaw : Measurable (fun volumeOutcome : VolumeOutcome =>
        ProbabilityTheory.poissonMeasure
          (volumeOutcome.2 / (R state).rate)) :=
      hpoisson.comp (measurable_snd.div measurable_const)
    have hweight : ∀ pending : Nat, Measurable (fun volumeOutcome : VolumeOutcome =>
        (ProbabilityTheory.poissonMeasure
          (volumeOutcome.2 / (R state).rate)) {pending}) := by
      intro pending
      exact (MeasureTheory.Measure.measurable_coe
        (measurableSet_singleton pending)).comp hlaw
    simp only [K]
    simp_rw [MeasureTheory.Measure.bind_apply hevent hHsection.aemeasurable,
      MeasureTheory.lintegral_countable']
    rw [MeasureTheory.lintegral_tsum]
    · congr 1
      funext pending
      exact MeasureTheory.lintegral_const_mul _ (hweight pending)
    · intro pending
      exact (measurable_const.mul (hweight pending)).aemeasurable
  simp_rw [hexpand]
  apply Measurable.tsum
  intro pending
  exact ((MeasureTheory.Measure.measurable_coe hevent).comp
      (hH.comp (hR.prodMk measurable_const))).mul
    ((measurable_volume_poisson_weight mu pending).comp hrate)

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · expanded both binds and used measurable Poisson coefficients
* this round · reduced · isolated the arbitrary volume-law parameterized bind
-/
