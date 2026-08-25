import Kr25Ssmxt.Analysis.MeasurablePoissonMeasure
import Kr25Ssmxt.Analysis.MeasurableThinSampleAdd

/-!
# Poisson draw followed by the thinning and sampling tail

This module isolates the step that threads an incoming state through a
state-dependent Poisson draw before invoking the remaining measurable kernel.
-/

namespace Kr25Ssmxt

/--
After a volume outcome has fixed the Poisson mean, the Poisson draw and all
remaining stages are jointly measurable in the state and volume outcome.

INTERNAL: state-threading through the countable Poisson stage of `processComponent`.
-/
lemma measurable_poisson_thin_tail {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n)
    (hpoisson : Measurable
      (fun r : NNReal => ProbabilityTheory.poissonMeasure r))
    (hadd : ∀ count, Measurable
      (fun z : TTCState n × (Fin count → LatticePoint n) => z.1.addBatch z.2))
    (hthin : Measurable
      (fun z : TTCState n × Nat => thinUntil z.1 z.2 threshold)) :
    Measurable (fun z : TTCState n × VolumeOutcome =>
      (ProbabilityTheory.poissonMeasure (z.2.2 / z.1.rate)).bind fun pending =>
        (thinUntil z.1 pending threshold).bind fun thinned =>
          (O.generateSamples P thinned.2 b epsilonPrime deltaPrime).bind fun batch =>
            (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst) := by
  have htail := measurable_thin_sample_add O b epsilonPrime deltaPrime threshold P
    hadd hthin
  let K : TTCState n × Nat → MeasureTheory.Measure (TTCState n) := fun z =>
    (thinUntil z.1 z.2 threshold).bind fun thinned =>
      (O.generateSamples P thinned.2 b epsilonPrime deltaPrime).bind fun batch =>
        (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst
  have hK : Measurable K := by
    simpa only [K] using htail
  change Measurable (fun z : TTCState n × VolumeOutcome =>
    (ProbabilityTheory.poissonMeasure (z.2.2 / z.1.rate)).bind fun pending =>
      K (z.1, pending))
  have hrate : Measurable (fun z : TTCState n × VolumeOutcome => z.1.rate) :=
    (measurable_fst.comp
      (comap_measurable (fun state : TTCState n =>
        (state.rate, state.samples, state.nextLabel)))).comp measurable_fst
  have hmean : Measurable
      (fun z : TTCState n × VolumeOutcome => z.2.2 / z.1.rate) :=
    (measurable_snd.comp measurable_snd).div hrate
  have hlaw : Measurable (fun z : TTCState n × VolumeOutcome =>
      ProbabilityTheory.poissonMeasure (z.2.2 / z.1.rate)) :=
    hpoisson.comp hmean
  refine MeasureTheory.Measure.measurable_of_measurable_coe _ ?_
  intro event hevent
  have hsection : ∀ z : TTCState n × VolumeOutcome,
      Measurable (fun pending : Nat => K (z.1, pending)) := by
    intro z
    exact hK.comp (measurable_const.prodMk measurable_id)
  simp_rw [MeasureTheory.Measure.bind_apply hevent (hsection _).aemeasurable,
    MeasureTheory.lintegral_countable']
  apply Measurable.tsum
  intro pending
  exact ((MeasureTheory.Measure.measurable_coe hevent).comp
      (hK.comp (measurable_fst.prodMk measurable_const))).mul
    ((MeasureTheory.Measure.measurable_coe (measurableSet_singleton pending)).comp hlaw)

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · expanded the countable Poisson integral as a measurable singleton sum
* this round · reduced · isolated state-threading through the varying Poisson law
-/
