import Kr25Ssmxt.Analysis.ProcessComponentsSamplesCardAEMeasurable
import Kr25Ssmxt.Analysis.TTCStateEstimateAEMeasurableOfSamplesCard

/-!
# Measurability of the TTC estimator

Cardinality is globally measurable on finite subsets of the countable coded-lattice sample
space. This file packages that fact for the law produced by the TTC component fold.
-/

namespace Kr25Ssmxt

/--
The public estimator is almost everywhere measurable under every law produced by the TTC
component fold.

INTERNAL: measurability bookkeeping restricted to states reachable by the TTC core.
-/
lemma processComponents_estimate_aemeasurable {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (Ps : List (PolytopeData n))
    (state : TTCState n) :
    AEMeasurable TTCState.estimate
      (processComponents O b epsilonPrime deltaPrime threshold Ps state) := by
  apply TTCState.estimate_aemeasurable_of_samples_card
  exact processComponents_samples_card_aemeasurable O b epsilonPrime deltaPrime threshold Ps state

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · updated · coded lattice samples make retained cardinality globally measurable
* previous round · proved by reduction · estimator arithmetic follows from sample cardinality
-/
