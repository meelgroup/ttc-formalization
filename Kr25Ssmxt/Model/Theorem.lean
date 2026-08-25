import Kr25Ssmxt.Model.Prior
import Kr25Ssmxt.Model.Pseudocode
import Kr25Ssmxt.Analysis.TheoremProof

namespace Kr25Ssmxt

/-!
PMF MODEL GAP: the desired discrete headline cannot yet be stated about the algorithm
defined in `Pseudocode.lean`.  In the current model, `ttc` has type `Measure NNReal`, its
oracles return `Measure`, and its adaptive control flow is assembled with `Measure.bind`.
Replacing the law below by an existentially chosen `PMF NNReal` would no longer measure
that algorithm.  Nor can `Measure.toPMF` repair the mismatch: its general construction
requires a `Countable` output type, while `NNReal` is uncountable, and in any case such a
post-hoc conversion would not expose the paper's random choices as `PMF.pure`/`PMF.bind`.

The measure-valued theorem below is the audit statement for the actual on-disk algorithm.
Its proof side additionally records a distinct model mismatch: `processComponent` uses a
Poisson mean `t / p`, while the paper uses `t * p`.  The empty-decomposition branch is
proved, but the nonempty accuracy argument is blocked until that rate convention is fixed.
-/

/--
TTC returns a probability law on single nonnegative estimates, and its estimate is within
relative error `ε` of the Lebesgue volume of the existentially projected real solution set
with probability at least `1 - δ`.  This is an accuracy statement only; it makes no runtime
claim.

PAPER: sections/analysis.tex:314-326
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
  exact ttc_volume_accuracy_proof hprior hn F hbounded params O hvolume hsamples

#modelClosureOfType ttc_volume_accuracy
#print axioms ttc_volume_accuracy

end Kr25Ssmxt
