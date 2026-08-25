import Kr25Ssmxt.Analysis.BatchFutureProfileMeasurable
import Kr25Ssmxt.Analysis.FutureMembershipProfile
import Kr25Ssmxt.Analysis.ProcessComponentProfileStep
import Kr25Ssmxt.Analysis.ProcessComponentsProfileStratifiedFalse

/-!
# Failure of deterministic profile stratification for the TTC component fold

The advertised output-law decomposition is false in the current measurable model.  For an
empty component list it would stratify a Dirac law by exact empty-suffix profiles and thereby
make sample cardinality almost-everywhere measurable.  The machine-checked theorem
`not_processComponents_profile_stratified_empty` refutes that conclusion at every empty-sample
state in dimension one.

The deterministic theorem can be revisited after the state measurable space exposes exact
finite configurations (in particular, after it has measurable singletons).  A law-level
replacement would instead need a supported-input invariant and would not imply this statement
for the current arbitrary deterministic input state.
-/

noncomputable section

namespace Kr25Ssmxt

open MeasureTheory

/--
The law produced by the TTC component fold is a countable sum of laws, each supported almost
everywhere on one exact final membership profile.

INTERNAL: discrete-trace stratification of removal, Poisson counts, thinning, sampling, and
finite collision patterns in the TTC component fold.
-/
lemma processComponents_profile_stratified {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (Ps : List (PolytopeData n))
    (state : TTCState n) :
    ∃ ν : Multiset (Nat × List Bool) → Measure (TTCState n),
      processComponents O b epsilonPrime deltaPrime threshold Ps state = Measure.sum ν ∧
      ∀ profile, ∀ᵐ s ∂ν profile, futureMembershipProfile [] s = profile := by
  -- DISPROVED: not_processComponents_profile_stratified_empty
  -- REPAIR: [MeasurableSingletonClass (TTCState n)]
  sorry

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · disproved · `not_processComponents_profile_stratified_empty`; the empty-list
  branch would force Dirac AE-measurability of sample cardinality
* this round · reduced · discharged carrier and finite batch-partition measurability; the
  remaining list-level obligation is induction, kernel measurability, and flattening countable
  sums using the separately stated one-component transition
* this round · reduced · isolated the full discrete-trace/profile decomposition required for
  the component fold
-/
