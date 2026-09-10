import Arlib.Probability.Poisson
import Kr25Ssmxt.Model.Prelude

/-!
# Poisson event probabilities as explicit mass sums

This file provides the measure-theoretic bridge between `poissonMeasure` and the
real-valued Poisson PMF used by the Chernoff estimates.
-/

noncomputable section

open scoped BigOperators NNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace Kr25Ssmxt

/--
The real probability of a Poisson event is the sum of its indicated point masses.

INTERNAL: Measure-to-PMF bridge needed to apply the explicit Chernoff sum bound.
-/
lemma poissonMeasure_real_eq_tsum_indicator (mean : NNReal) (S : Set Nat) :
    (poissonMeasure mean).real S =
      ∑' k : Nat, if k ∈ S then Arlib.Probability.poissonPMF (mean : Real) k else 0 := by
  rw [← MeasureTheory.integral_indicator_one (MeasurableSet.of_discrete S)]
  rw [ProbabilityTheory.integral_poissonMeasure]
  apply tsum_congr
  intro k
  by_cases hk : k ∈ S
  · simp [Set.indicator, hk, Arlib.Probability.poissonPMF]
  · simp [Set.indicator, hk]

end Kr25Ssmxt
