import Kr25Ssmxt.Analysis.FairCoinStreamLawIsProbabilityMeasure
import Kr25Ssmxt.Analysis.MeasurableThinningResult

/-!
# Normalization of TTC thinning

Pushing the fair coin stream through the measurable first-exit result preserves total mass.
-/

namespace Kr25Ssmxt

/--
Every invocation of `thinUntil` is a probability measure.

INTERNAL: normalization bookkeeping for the TTC thinning construction.
-/
lemma thinUntil_isProbabilityMeasure {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) :
    MeasureTheory.IsProbabilityMeasure (thinUntil s pending threshold) := by
  letI : MeasureTheory.IsProbabilityMeasure fairCoinStreamLaw :=
    fairCoinStreamLaw_isProbabilityMeasure
  unfold thinUntil
  exact MeasureTheory.Measure.isProbabilityMeasure_map
    (measurable_thinningResult s pending threshold).aemeasurable

end Kr25Ssmxt
