import Kr25Ssmxt.Analysis.FutureMembershipProfileMeasurableSpace
import Kr25Ssmxt.Analysis.MeasureSumByCountableAeFibers

/-!
# Deterministic profile stratification for the TTC component fold

The lattice-coded sample representation makes the exact final profile globally measurable.
Every component-fold output law can therefore be split directly over its countable fibers.
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
  exact measure_sum_by_countable_ae_fibers _ _
    (futureMembershipProfile_measurable ([] : List (PolytopeData n))).aemeasurable

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · split the output law directly over globally measurable countable profiles
* previous round · reopened · lattice-coded samples removed the former empty-list obstruction
-/
