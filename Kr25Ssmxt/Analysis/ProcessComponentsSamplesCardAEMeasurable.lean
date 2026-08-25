import Kr25Ssmxt.Analysis.CardAEMeasurableOfFixedCardSum
import Kr25Ssmxt.Analysis.ProcessComponentsProfileStratified

/-!
# Reachable retained-sample cardinality is almost everywhere measurable

This is the finite-configuration obligation hidden by the membership-generated measurable
space on `Finset`.  It is deliberately restricted to laws produced by the TTC component fold;
global measurability of `Finset.card` is unavailable for the uncountable point type.
-/

namespace Kr25Ssmxt

/--
The number of retained copies has an almost-everywhere measurable version under a state law
produced by the TTC component fold.

INTERNAL: reachable finite-configuration measurability needed to map the final state law through
the estimator.
-/
lemma processComponents_samples_card_aemeasurable {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (Ps : List (PolytopeData n))
    (state : TTCState n) :
    AEMeasurable (fun s : TTCState n => s.samples.card)
      (processComponents O b epsilonPrime deltaPrime threshold Ps state) := by
  obtain ⟨ν, hsum, hprofile⟩ :=
    processComponents_profile_stratified O b epsilonPrime deltaPrime threshold Ps state
  rw [hsum]
  apply card_aemeasurable_of_fixedCard_sum ν fun profile => profile.card
  intro profile
  filter_upwards [hprofile profile] with s hs
  rw [← futureMembershipProfile_card ([] : List (PolytopeData n)) s, hs]

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved by reduction · converted exact empty-suffix profile strata into
  fixed-cardinality strata
* this round · reduced · isolated the reachable-cardinality property missing from the current
  membership-generated `Finset` measurable structure
-/
