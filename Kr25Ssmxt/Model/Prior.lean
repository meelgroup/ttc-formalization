import Kr25Ssmxt.Model.Prelude

/-!
# What this development assumes

The results this proof takes from prior work — cited, standard, or folklore — are stated
as hypotheses.  The capstone carries `(hprior : Prior)`, so the remaining external
probability result is visible in its statement rather than hidden in a proof body.
-/

namespace Kr25Ssmxt

/-- Every result this development takes from prior work rather than proving.

The field is the Poissonized finite-union streaming theorem used by the paper's
`lem:process`/`lem:numlattice` argument, restricted to its valid high-intensity regime.
The headline theorem exposes that regime as a premise.
-/
structure Prior : Prop where
  streamingCoreAccuracy :
    ∀ {n k : Nat} (F : LRAFormula n k)
      (hbounded : Bornology.IsBounded (solutionSet F))
      (params : ApproxParams) (O : TTCOracles n k),
      StreamingCoreAccuracy F hbounded params O

end Kr25Ssmxt
