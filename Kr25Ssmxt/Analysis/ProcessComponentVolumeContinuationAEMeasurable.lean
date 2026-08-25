import Kr25Ssmxt.Analysis.MeasurablePoissonMeasure

/-!
# Measurability of the volume-outcome component continuation

The continuation from a volume outcome through the remaining Poisson, thinning, and
sampling stages is almost everywhere measurable under the volume-oracle law.
-/

namespace Kr25Ssmxt

/--
The continuation after the volume oracle is measurable enough for `Measure.bind`.

INTERNAL: Giry-monad bookkeeping for normalization of one TTC component step.
-/
lemma processComponent_volume_continuation_aemeasurable {n k : Nat}
    (O : TTCOracles n k) (b : Nat) (epsilonPrime deltaPrime threshold : Real)
    (P : PolytopeData n) (s : TTCState n) :
    AEMeasurable
      (fun volumeOutcome : VolumeOutcome =>
        let withoutDuplicates := s.removeComponent P
        (ProbabilityTheory.poissonMeasure
          (volumeOutcome.2 / withoutDuplicates.rate)).bind fun pending =>
            (thinUntil withoutDuplicates pending threshold).bind fun thinned =>
              (O.generateSamples P thinned.2 b epsilonPrime deltaPrime).bind fun batch =>
                (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst)
      (O.computeVolume P epsilonPrime deltaPrime) := by
  let withoutDuplicates := s.removeComponent P
  let afterPending : Nat → MeasureTheory.Measure (TTCState n) := fun pending =>
    (thinUntil withoutDuplicates pending threshold).bind fun thinned =>
      (O.generateSamples P thinned.2 b epsilonPrime deltaPrime).bind fun batch =>
        (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst
  have hAfterPending : Measurable afterPending := Measurable.of_discrete
  have hRate : Measurable
      (fun volumeOutcome : VolumeOutcome => volumeOutcome.2 / withoutDuplicates.rate) :=
    (measurable_snd : Measurable (fun volumeOutcome : VolumeOutcome => volumeOutcome.2)).div_const _
  have hPoisson : Measurable (fun volumeOutcome : VolumeOutcome =>
      ProbabilityTheory.poissonMeasure
        (volumeOutcome.2 / withoutDuplicates.rate)) :=
    measurable_poissonMeasure.comp hRate
  have hContinuation : Measurable (fun volumeOutcome : VolumeOutcome =>
      (ProbabilityTheory.poissonMeasure
        (volumeOutcome.2 / withoutDuplicates.rate)).bind afterPending) :=
    (MeasureTheory.Measure.measurable_bind' hAfterPending).comp hPoisson
  have hContinuationAE : AEMeasurable (fun volumeOutcome : VolumeOutcome =>
      (ProbabilityTheory.poissonMeasure
        (volumeOutcome.2 / withoutDuplicates.rate)).bind afterPending)
      (O.computeVolume P epsilonPrime deltaPrime) :=
    hContinuation.aemeasurable
  simpa [withoutDuplicates, afterPending] using
    hContinuationAE

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · used discreteness of the Poisson count and measurable Giry bind
* r1 · reduced · isolated the outer volume continuation measurability obligation
-/
