import Kr25Ssmxt.Analysis.FairCoinStreamLawIsProbabilityMeasure
import Kr25Ssmxt.Analysis.MeasurableAddBatch
import Kr25Ssmxt.Analysis.MeasurableThinningResultJoint

/-!
# Measurability of the final component-step continuation

The final sample-batch continuation, including its second thinning pass and state
projection, is almost everywhere measurable under the corresponding sample law.
-/

namespace Kr25Ssmxt

/--
The continuation after a generated batch is measurable enough for `Measure.bind`.

INTERNAL: Giry-monad bookkeeping for normalization of one TTC component step.
-/
lemma processComponent_batch_continuation_aemeasurable {n k : Nat}
    (O : TTCOracles n k) (b : Nat) (epsilonPrime deltaPrime threshold : Real)
    (P : PolytopeData n) (thinned : TTCState n × Nat) :
    AEMeasurable
      (fun batch : SampleBatch n thinned.2 =>
        (thinUntil (thinned.1.addBatch batch.2) 0 threshold).map Prod.fst)
      (O.generateSamples P thinned.2 b epsilonPrime deltaPrime) := by
  let _ : MeasureTheory.IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let result := fun z : SampleBatch n thinned.2 × (Nat × Nat → Bool) =>
    thinningResult (thinned.1.addBatch z.1.2) 0 threshold z.2
  have hstate : Measurable (fun z : SampleBatch n thinned.2 × (Nat × Nat → Bool) =>
      thinned.1.addBatch z.1.2) :=
    measurable_addBatch.comp
      (measurable_const.prodMk (measurable_snd.comp measurable_fst))
  have hresult : Measurable result :=
    (measurable_thinningResult_joint threshold).comp
      ((hstate.prodMk measurable_const).prodMk measurable_snd)
  have hfst : Measurable (fun z => (result z).1) :=
    measurable_fst.comp hresult
  have hparameterized : Measurable (fun batch : SampleBatch n thinned.2 =>
      fairCoinStreamLaw.map (fun coins => (result (batch, coins)).1)) := by
    have h := (MeasureTheory.Measure.measurable_map _ hfst).comp
      (Measurable.map_prodMk_left (ν := fairCoinStreamLaw))
    convert h using 1
    funext batch
    have hembed : Measurable (fun coins : Nat × Nat → Bool => (batch, coins)) :=
      measurable_const.prodMk measurable_id
    change fairCoinStreamLaw.map (fun coins => (result (batch, coins)).1) =
      (fairCoinStreamLaw.map (Prod.mk batch)).map (fun z => (result z).1)
    rw [MeasureTheory.Measure.map_map hfst hembed]
    rfl
  apply Measurable.aemeasurable
  unfold thinUntil
  convert hparameterized using 1
  funext batch
  have hsection : Measurable
      (thinningResult (thinned.1.addBatch batch.2) 0 threshold) := by
    have hembed : Measurable (fun coins : Nat × Nat → Bool => (batch, coins)) :=
      measurable_const.prodMk measurable_id
    have h := hresult.comp hembed
    change Measurable (fun coins : Nat × Nat → Bool =>
      thinningResult (thinned.1.addBatch batch.2) 0 threshold coins) at h
    exact h
  rw [MeasureTheory.Measure.map_map measurable_fst
    hsection]
  rfl

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · parameterized the jointly measurable thinning result by the fixed fair-coin law
* r1 · reduced · isolated the final sample-batch continuation measurability obligation
-/
