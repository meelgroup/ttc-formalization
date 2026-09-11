import Kr25Ssmxt.Model.Program
import Kr25Ssmxt.Analysis.CV18HitAndRunOracles

/-!
# The concrete TTC run

The oracle-parametric TTC engine lives in `Model.Program`.  This audit-facing entry point
fixes its two geometric routines to
the current arlib-community CV18 volume algorithm and finite-step Hit-and-Run/KV97 sampler.
-/

noncomputable section

open MeasureTheory

namespace Kr25Ssmxt

/-- TTC with its geometric routines fixed to the current arlib-community implementations. -/
def communityTTC {n k : Nat} (hn : 21 ≤ n) (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F)) (params : ApproxParams)
    (prep : TTCPreprocessor n k) : Measure NNReal :=
  ttc F hbounded params (communityCV18HitAndRunOracles hn prep)

end Kr25Ssmxt
