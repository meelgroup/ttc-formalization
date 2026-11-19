import ttc.Analysis.ReferenceProgram

/-!
# Normalization of one fair coin

The Bernoulli law used by TTC is a probability measure.
-/

namespace ttc

/--
`fairCoinLaw` has total mass one.

INTERNAL: normalization bookkeeping for the TTC thinning construction.
-/
lemma fairCoinLaw_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure fairCoinLaw := by
  unfold fairCoinLaw
  infer_instance

end ttc
