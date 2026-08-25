import Kr25Ssmxt.Analysis.MeasurableThinningResultJoint
import Kr25Ssmxt.Analysis.FairCoinStreamLawIsProbabilityMeasure

/-!
# Measurability of the thinning kernel

This packages joint thinning-result measurability as the measure-valued
transition used by both thinning calls in `processComponent`.
-/

namespace Kr25Ssmxt

/--
For a fixed threshold, `thinUntil` is a measurable kernel in the state and
pending count.

INTERNAL: measure-valued kernel bookkeeping for the TTC thinning loop.
-/
lemma thinUntil_kernel_measurable {n : Nat} (threshold : Real) :
    Measurable (fun z : TTCState n × Nat => thinUntil z.1 z.2 threshold) := by
  let _ : MeasureTheory.IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  let G := fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
    thinningResult z.1.1 z.1.2 threshold z.2
  have hG : Measurable G := measurable_thinningResult_joint threshold
  have hpair : Measurable
      (fun z : TTCState n × Nat => fairCoinStreamLaw.map (Prod.mk z)) :=
    Measurable.map_prodMk_left
  have hmap : Measurable
      (fun z : TTCState n × Nat =>
        (fairCoinStreamLaw.map (Prod.mk z)).map G) :=
    (MeasureTheory.Measure.measurable_map G hG).comp hpair
  have heq :
      (fun z : TTCState n × Nat =>
        (fairCoinStreamLaw.map (Prod.mk z)).map G) =
      (fun z : TTCState n × Nat => thinUntil z.1 z.2 threshold) := by
    funext z
    rw [MeasureTheory.Measure.map_map hG measurable_prodMk_left]
    unfold thinUntil
    congr 1
  rw [← heq]
  exact hmap

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · used joint thinning measurability and measurable pushforward composition
* this round · proved · expressed varying pushforwards as sections of one jointly measurable event
* this round · reduced · isolated the parameterized pushforward from joint thinning measurability
-/
