import Kr25Ssmxt.Model.Prelude

/-!
# Retained-sample cardinality is measurable

The sampler state is a finite set over the countable type of coded decimal-lattice points.
Consequently its cardinality is globally measurable; no reachable-law stratification is needed.
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
  have hsamples : Measurable (fun s : TTCState n => s.samples) :=
    (measurable_fst.comp measurable_snd).comp
      (comap_measurable (fun s : TTCState n => (s.rate, s.samples, s.nextLabel)))
  exact ((measurable_of_countable (fun samples : Finset (SampleCopy n) => samples.card)).comp
    hsamples).aemeasurable

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · countability of coded lattice samples makes `Finset.card` measurable
* previous round · reduced · used reachable-profile stratification for arbitrary real samples
-/
