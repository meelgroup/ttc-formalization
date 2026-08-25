import Kr25Ssmxt.Model.Prior
import Kr25Ssmxt.Model.Pseudocode

namespace Kr25Ssmxt

/-!
PMF MODEL GAP: the desired discrete headline cannot yet be stated about the algorithm
defined in `Pseudocode.lean`.  In the current model, `ttc` has type `Measure NNReal`, its
oracles return `Measure`, and its adaptive control flow is assembled with `Measure.bind`.
Replacing the law below by an existentially chosen `PMF NNReal` would no longer measure
that algorithm.  Nor can `Measure.toPMF` repair the mismatch: its general construction
requires a `Countable` output type, while `NNReal` is uncountable, and in any case such a
post-hoc conversion would not expose the paper's random choices as `PMF.pure`/`PMF.bind`.

This theorem therefore records the paper's probability bound for the actual on-disk
algorithm until the randomized primitives and control flow in `Pseudocode.lean` are
changed to return `PMF` directly.
-/

/--
TTC returns a probability law on single nonnegative estimates, and its estimate is within
relative error `ε` of the Lebesgue volume of the existentially projected real solution set
with probability at least `1 - δ`.  This is an accuracy statement only; it makes no runtime
claim.
-/
theorem ttc_volume_accuracy
    (hprior : Prior)
    {n k : Nat}
    (hn : 0 < n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (O : TTCOracles n k)
    (hvolume : ComputeVolumeContract O F hbounded params)
    (hsamples : GenerateSamplesContract O F hbounded params) :
    MeasureTheory.IsProbabilityMeasure (ttc F hbounded params O) ∧
      (ttc F hbounded params O).real
          {estimate | (estimate : Real) ∈
            Arlib.relErr params.epsilon
              (MeasureTheory.volume (solutionSet F)).toReal} ≥
        1 - params.delta := by
  sorry

#modelClosureOfType ttc_volume_accuracy
#print axioms ttc_volume_accuracy

end Kr25Ssmxt
