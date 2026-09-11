import Kr25Ssmxt.Model.Program

/-!
# Measurability of the TTC estimate from measurable sample count

The estimator is a measurable arithmetic expression once the retained-sample cardinality
has an almost-everywhere measurable version under the state law in question.
-/

namespace Kr25Ssmxt

open MeasureTheory

/--
Almost-everywhere measurability of retained-sample cardinality implies the same property for
the public estimator.

INTERNAL: separates the measurable arithmetic in the estimator from the finite-configuration
measurability needed for reachable TTC states.
-/
lemma TTCState.estimate_aemeasurable_of_samples_card {n : Nat} {mu : Measure (TTCState n)}
    (hcard : AEMeasurable (fun s : TTCState n => s.samples.card) mu) :
    AEMeasurable TTCState.estimate mu := by
  have hrate : Measurable (fun s : TTCState n => s.rate) :=
    measurable_fst.comp (comap_measurable (fun s : TTCState n =>
      (s.rate, s.samples, s.nextLabel)))
  have hcardNN : AEMeasurable
      (fun s : TTCState n => (s.samples.card : NNReal)) mu :=
    (measurable_of_countable (fun count : Nat => (count : NNReal))).comp_aemeasurable hcard
  change AEMeasurable
    (fun s : TTCState n => (s.samples.card : NNReal) / s.rate) mu
  exact hcardNN.div hrate.aemeasurable

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · reduced estimator measurability to the retained-cardinality coordinate
-/
