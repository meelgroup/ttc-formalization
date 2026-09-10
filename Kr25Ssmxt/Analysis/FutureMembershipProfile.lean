import Kr25Ssmxt.Model.Prelude

/-!
# Future-component membership profiles

This file records exactly the discrete information about a retained sample configuration
that is relevant to a suffix of the component-processing loop.  Multiplicity is retained by
using a multiset rather than a finset.
-/

noncomputable section

namespace Kr25Ssmxt

/--
The label and future-component membership bits of every retained sample copy.

INTERNAL: countable discrete state used to stratify laws produced by the TTC component fold.
-/
def futureMembershipProfile {n : Nat} (Qs : List (PolytopeData n)) (s : TTCState n) :
    Multiset (Nat × List Bool) := by
  classical
  exact s.samples.1.map fun copy =>
    (copy.1, Qs.map fun Q => decide (copy.2.toPoint ∈ Q.carrier))

/--
Profiling changes the information attached to each retained copy, but does not change the
number of copies.

INTERNAL: the empty-suffix profile length recovers the estimator's sample cardinality.
-/
lemma futureMembershipProfile_card {n : Nat} (Qs : List (PolytopeData n))
    (s : TTCState n) :
    (futureMembershipProfile Qs s).card = s.samples.card := by
  simp [futureMembershipProfile]

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · introduced multiset-valued suffix profiles and proved their length is
  exactly retained-sample cardinality
-/
