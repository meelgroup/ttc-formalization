import Kr25Ssmxt.Model.Program

/-!
# Almost-everywhere measurability on fixed-cardinality strata

A countable sum of state measures, each concentrated on a fixed sample cardinality, admits
sample cardinality as an almost-everywhere measurable observable.
-/

namespace Kr25Ssmxt

open MeasureTheory

/--
Sample cardinality is almost everywhere measurable for a countable sum of measures on which
it is separately almost everywhere constant.

INTERNAL: converts the discrete trace decomposition of TTC into the measurability needed by
the final estimator map.
-/
lemma card_aemeasurable_of_fixedCard_sum {n : Nat} {ι : Type*} [Countable ι]
    (ν : ι → Measure (TTCState n)) (fixedCard : ι → Nat)
    (hcard : ∀ i, ∀ᵐ s ∂ν i, s.X.card = fixedCard i) :
    AEMeasurable (fun s : TTCState n => s.X.card) (Measure.sum ν) := by
  apply AEMeasurable.sum_measure
  intro i
  apply aemeasurable_const.congr
  filter_upwards [hcard i] with s hs
  exact hs.symm

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · combined measurable constant representatives with
  `AEMeasurable.sum_measure`
-/
