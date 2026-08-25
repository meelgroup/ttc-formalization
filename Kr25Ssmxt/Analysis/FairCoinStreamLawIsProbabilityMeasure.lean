import Kr25Ssmxt.Analysis.FairCoinLawIsProbabilityMeasure

/-!
# Normalization of the fair coin stream

The independent product of TTC's fair coin laws is a probability measure.
-/

namespace Kr25Ssmxt

/--
`fairCoinStreamLaw` has total mass one.

INTERNAL: normalization bookkeeping for the TTC thinning construction.
-/
lemma fairCoinStreamLaw_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure fairCoinStreamLaw := by
  letI (_ : Nat × Nat) : MeasureTheory.IsProbabilityMeasure fairCoinLaw :=
    fairCoinLaw_isProbabilityMeasure
  unfold fairCoinStreamLaw
  infer_instance

end Kr25Ssmxt
