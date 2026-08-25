import Kr25Ssmxt.Analysis.MeasurableAddBatch
import Kr25Ssmxt.Analysis.ThinUntilKernelMeasurable

/-!
# Fixed-count sampling and insertion tail

This module isolates the fixed dependent sample type in the final sampling and
thinning stages of one TTC component iteration.  The fixed sample type is
countable, so an arbitrary sample law can be expanded over singleton batches;
this avoids any s-finiteness assumption on `TTCOracles.generateSamples`.
-/

namespace Kr25Ssmxt

/--
For a fixed generated batch size, sampling, inserting the batch, and performing
the final thinning pass form a measurable state-indexed measure.

INTERNAL: fixed-count parameterized bind in the `processComponent` kernel.
-/
lemma measurable_sample_add_fixed {n k : Nat} (O : TTCOracles n k) (b count : Nat)
    (epsilonPrime deltaPrime threshold : Real) (P : PolytopeData n)
    (hadd : Measurable
      (fun z : TTCState n × (Fin count → LatticePoint n) => z.1.addBatch z.2))
    (hthin : Measurable
      (fun z : TTCState n × Nat => thinUntil z.1 z.2 threshold)) :
    Measurable (fun state : TTCState n =>
      (O.generateSamples P count b epsilonPrime deltaPrime).bind fun batch =>
        (thinUntil (state.addBatch batch.2) 0 threshold).map Prod.fst) := by
  let μ := O.generateSamples P count b epsilonPrime deltaPrime
  let K := fun z : TTCState n × SampleBatch n count =>
    (thinUntil (z.1.addBatch z.2.2) 0 threshold).map Prod.fst
  have hadded : Measurable (fun z : TTCState n × SampleBatch n count =>
      z.1.addBatch z.2.2) :=
    hadd.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hthinned : Measurable (fun z : TTCState n × SampleBatch n count =>
      thinUntil (z.1.addBatch z.2.2) 0 threshold) :=
    hthin.comp (hadded.prodMk measurable_const)
  have hK : Measurable K :=
    (MeasureTheory.Measure.measurable_map _ measurable_fst).comp hthinned
  change Measurable (fun state : TTCState n => μ.bind fun batch => K (state, batch))
  apply MeasureTheory.Measure.measurable_of_measurable_coe
  intro A hA
  have hsection (state : TTCState n) :
      Measurable (fun batch : SampleBatch n count => K (state, batch)) :=
    hK.comp (measurable_const.prodMk measurable_id)
  have hsum : Measurable (fun state : TTCState n =>
      ∑' batch : SampleBatch n count, K (state, batch) A * μ {batch}) :=
    Measurable.tsum fun batch =>
      ((MeasureTheory.Measure.measurable_coe hA).comp
        (hK.comp (measurable_id.prodMk measurable_const))).mul measurable_const
  convert hsum using 1
  funext state
  rw [MeasureTheory.Measure.bind_apply hA (hsection state).aemeasurable,
    MeasureTheory.lintegral_countable']

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · expanded the arbitrary fixed sample law over the countable batch type
* this round · blocked · proved joint measurability of the continuation; the fixed sample law has no `SFinite` hypothesis
* this round · reduced · isolated the arbitrary sample-law parameterized bind at fixed count
-/
