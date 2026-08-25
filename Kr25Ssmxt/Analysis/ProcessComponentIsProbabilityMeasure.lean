import Kr25Ssmxt.Analysis.ProcessComponentKernelMeasurable
import Kr25Ssmxt.Analysis.ProcessComponentBatchContinuationAEMeasurable
import Kr25Ssmxt.Analysis.ProcessComponentThinnedContinuationAEMeasurable
import Kr25Ssmxt.Analysis.ProcessComponentVolumeContinuationAEMeasurable
import Kr25Ssmxt.Analysis.ThinUntilIsProbabilityMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Normalization of one TTC component step

One component step preserves total probability when both oracle families are normalized.
-/

namespace Kr25Ssmxt

/--
Normalized volume and sample oracles make every invocation of `processComponent` a
probability measure.

INTERNAL: normalization bookkeeping for one iteration of the TTC streaming core.
-/
lemma processComponent_isProbabilityMeasure {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n)
    (hvolume : MeasureTheory.IsProbabilityMeasure
      (O.computeVolume P epsilonPrime deltaPrime))
    (hsamples : ∀ count, MeasureTheory.IsProbabilityMeasure
      (O.generateSamples P count b epsilonPrime deltaPrime))
    (s : TTCState n) :
    MeasureTheory.IsProbabilityMeasure
      (processComponent O b epsilonPrime deltaPrime threshold P s) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (O.computeVolume P epsilonPrime deltaPrime) := hvolume
  unfold processComponent
  apply MeasureTheory.isProbabilityMeasure_bind
    (processComponent_volume_continuation_aemeasurable
      O b epsilonPrime deltaPrime threshold P s)
  filter_upwards with volumeOutcome
  let withoutDuplicates := s.removeComponent P
  apply MeasureTheory.isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
  filter_upwards with pending
  letI : MeasureTheory.IsProbabilityMeasure
      (thinUntil withoutDuplicates pending threshold) :=
    thinUntil_isProbabilityMeasure withoutDuplicates pending threshold
  apply MeasureTheory.isProbabilityMeasure_bind
    (processComponent_thinned_continuation_aemeasurable
      O b epsilonPrime deltaPrime threshold P hsamples withoutDuplicates pending)
  filter_upwards with thinned
  letI : MeasureTheory.IsProbabilityMeasure
      (O.generateSamples P thinned.2 b epsilonPrime deltaPrime) := hsamples thinned.2
  apply MeasureTheory.isProbabilityMeasure_bind
    (processComponent_batch_continuation_aemeasurable
      O b epsilonPrime deltaPrime threshold P thinned)
  filter_upwards with batch
  letI : MeasureTheory.IsProbabilityMeasure
      (thinUntil (thinned.1.addBatch batch.2) 0 threshold) :=
    thinUntil_isProbabilityMeasure (thinned.1.addBatch batch.2) 0 threshold
  exact MeasureTheory.Measure.isProbabilityMeasure_map (by fun_prop)

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · repaired the parked proof after the post-thinning lemma gained `hsamples`
* r1 · reduced · isolated normalization behind three continuation-measurability lemmas
-/
