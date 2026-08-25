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
  letI : MeasureTheory.IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  apply MeasureTheory.Measure.measurable_of_measurable_coe
  intro A hA
  unfold thinUntil
  simp_rw [MeasureTheory.Measure.map_apply
    (measurable_thinningResult _ _ threshold) hA]
  let J : Set ((TTCState n × Nat) × (Nat × Nat → Bool)) :=
    {q | thinningResult q.1.1 q.1.2 threshold q.2 ∈ A}
  have hJ : MeasurableSet J := by
    exact (measurable_thinningResult_joint threshold) hA
  let κ : ProbabilityTheory.Kernel (TTCState n × Nat) (Nat × Nat → Bool) :=
    ProbabilityTheory.Kernel.const (TTCState n × Nat) fairCoinStreamLaw
  have hsection := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
    (κ := κ) hJ
  simpa [κ, J] using hsection

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · expressed varying pushforwards as sections of one jointly measurable event
* this round · reduced · isolated the parameterized pushforward from joint thinning measurability
-/
