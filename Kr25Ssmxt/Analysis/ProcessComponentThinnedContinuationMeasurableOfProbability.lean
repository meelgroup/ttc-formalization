import Kr25Ssmxt.Analysis.MeasurableAddBatch
import Kr25Ssmxt.Analysis.MeasurableFixedSfiniteBind
import Kr25Ssmxt.Analysis.ThinUntilKernelMeasurable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Measurability of the post-thinning continuation

Probability sample oracles are s-finite, so their binds against the jointly measurable
batch-insertion and final-thinning kernel vary measurably with the thinned state.
-/

namespace Kr25Ssmxt

/--
The continuation after the first thinning pass is globally measurable when every sample
oracle invocation is a probability measure.

INTERNAL: Giry-monad bookkeeping for normalization of one TTC component step.
-/
lemma processComponent_thinned_continuation_measurable_of_probability {n k : Nat}
    (O : TTCOracles n k) (b : Nat) (epsilonPrime deltaPrime threshold : Real)
    (P : PolytopeData n)
    (hsamples : ∀ count, MeasureTheory.IsProbabilityMeasure
      (O.generateSamples P count b epsilonPrime deltaPrime)) :
    Measurable
      (fun thinned : TTCState n × Nat =>
        (O.generateSamples P thinned.2 b epsilonPrime deltaPrime).bind fun batch =>
          (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst) := by
  apply measurable_from_prod_countable_left
  intro count
  let μ := O.generateSamples P count b epsilonPrime deltaPrime
  let K := fun z : TTCState n × SampleBatch n count =>
    (thinUntil (z.1.addBatch z.2.2) 0 threshold).map Prod.fst
  have hadded : Measurable (fun z : TTCState n × SampleBatch n count =>
      z.1.addBatch z.2.2) :=
    measurable_addBatch.comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hthin : Measurable (fun z : TTCState n × SampleBatch n count =>
      thinUntil (z.1.addBatch z.2.2) 0 threshold) :=
    (thinUntil_kernel_measurable threshold).comp
      (hadded.prodMk measurable_const)
  have hK : Measurable K :=
    (MeasureTheory.Measure.measurable_map _ measurable_fst).comp hthin
  letI : MeasureTheory.IsProbabilityMeasure μ := hsamples count
  exact measurable_fixed_sfinite_bind μ K hK

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · assembled fixed-count s-finite binds over the discrete count coordinate
-/
