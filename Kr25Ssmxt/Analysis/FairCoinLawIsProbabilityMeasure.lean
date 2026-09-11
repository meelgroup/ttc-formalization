import Kr25Ssmxt.Model.Program

/-!
# Normalization of one fair coin

The Bernoulli law used by TTC is a probability measure.
-/

namespace Kr25Ssmxt

/--
`fairCoinLaw` has total mass one.

INTERNAL: normalization bookkeeping for the TTC thinning construction.
-/
lemma fairCoinLaw_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure fairCoinLaw := by
  unfold fairCoinLaw
  infer_instance

end Kr25Ssmxt
