import Kr25Ssmxt.Analysis.ReferenceProgram

/-!
# Measurability of the Poisson law in its rate

The first state-dependent random law in one TTC component is measurable as a
measure-valued function of its nonnegative rate.
-/

namespace Kr25Ssmxt

/--
The Poisson distribution is measurable in its rate parameter.

INTERNAL: parameter measurability for the Poisson stage of `processComponent`.
-/
lemma measurable_poissonMeasure :
    Measurable (fun r : NNReal => ProbabilityTheory.poissonMeasure r) := by
  refine MeasureTheory.Measure.measurable_of_measurable_coe _ fun s hs => ?_
  change Measurable (fun r : NNReal =>
    (MeasureTheory.Measure.sum (fun n =>
      ENNReal.ofReal (Real.exp (-r) * r ^ n / Nat.factorial n) •
        (MeasureTheory.Measure.dirac n))) s)
  simp_rw [MeasureTheory.Measure.sum_apply _ hs, MeasureTheory.Measure.smul_apply,
    smul_eq_mul, MeasureTheory.Measure.dirac_apply' _ hs]
  exact Measurable.tsum fun _ => by fun_prop

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · expanded singleton masses and used measurable countable summation
-/
