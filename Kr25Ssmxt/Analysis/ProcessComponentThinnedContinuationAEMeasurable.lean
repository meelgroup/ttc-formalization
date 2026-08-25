import Kr25Ssmxt.Analysis.ProcessComponentThinnedContinuationMeasurableOfProbability

/-!
# Measurability of the post-thinning component continuation

The continuation from the first thinning result through sample generation and the final
thinning pass is almost everywhere measurable under the first thinning law when the
sample-oracle laws are probability measures.
-/

namespace Kr25Ssmxt

/--
The continuation after the first thinning pass is measurable enough for `Measure.bind`
when every possible sample-count invocation is normalized.

INTERNAL: Giry-monad bookkeeping for normalization of one TTC component step.
-/
lemma processComponent_thinned_continuation_aemeasurable {n k : Nat}
    (O : TTCOracles n k) (b : Nat) (epsilonPrime deltaPrime threshold : Real)
    (P : PolytopeData n)
    (hsamples : ∀ count, MeasureTheory.IsProbabilityMeasure
      (O.generateSamples P count b epsilonPrime deltaPrime))
    (withoutDuplicates : TTCState n) (pending : Nat) :
    AEMeasurable
      (fun thinned : TTCState n × Nat =>
        (O.generateSamples P thinned.2 b epsilonPrime deltaPrime).bind fun batch =>
          (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst)
      (thinUntil withoutDuplicates pending threshold) := by
  exact (processComponent_thinned_continuation_measurable_of_probability
    O b epsilonPrime deltaPrime threshold P hsamples).aemeasurable

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · repaired · added `hsamples`; arbitrary oracle measures need not support measurable parameterized binds
* r1 · reduced · isolated the post-thinning continuation measurability obligation
-/
