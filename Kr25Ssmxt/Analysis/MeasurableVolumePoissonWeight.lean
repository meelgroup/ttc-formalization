import Kr25Ssmxt.Analysis.MeasurablePoissonMeasure
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Measurability of an averaged Poisson singleton weight

This module isolates the only nonstandard parameter-integral in the measurable
component kernel.  The averaging measure is deliberately arbitrary: the volume
oracle's probability-measure contract is introduced only downstream.
-/

namespace Kr25Ssmxt

open Filter MeasureTheory Set
open scoped Topology

/--
For a fixed pending count, averaging its Poisson mass over an arbitrary volume
outcome law is measurable in the denominator rate.

INTERNAL: coefficient obtained by expanding the volume and Poisson binds into a
countable sum; its proof uses lower semicontinuity away from rate zero and a
measurable singleton split at zero.
-/
lemma measurable_volume_poisson_weight
    (mu : MeasureTheory.Measure VolumeOutcome) (pending : Nat) :
    Measurable (fun r : NNReal =>
      ∫⁻ v, (ProbabilityTheory.poissonMeasure (v.2 / r)) {pending} ∂mu) := by
  apply measurable_of_measurable_on_compl_singleton 0
  apply LowerSemicontinuous.measurable
  rw [lowerSemicontinuous_restrict_iff]
  rw [lowerSemicontinuousOn_iff_le_liminf]
  intro r hr
  let _ := nhdsWithin_neBot_of_mem hr
  calc
    (∫⁻ v, (ProbabilityTheory.poissonMeasure (v.2 / r)) {pending} ∂mu) =
        ∫⁻ v, liminf (fun q : NNReal =>
          (ProbabilityTheory.poissonMeasure (v.2 / q)) {pending})
          (𝓝[{q : NNReal | q ≠ 0}] r) ∂mu := by
      congr 1 with v
      apply Eq.symm
      apply Filter.Tendsto.liminf_eq
      simp_rw [ProbabilityTheory.poissonMeasure_singleton]
      have hmean : ContinuousWithinAt (fun q : NNReal => v.2 / q)
          {q : NNReal | q ≠ 0} r :=
        (continuousAt_const.div continuousAt_id hr).continuousWithinAt
      have hmeanReal : ContinuousWithinAt
          (fun q : NNReal => ((v.2 / q : NNReal) : Real))
          {q : NNReal | q ≠ 0} r :=
        NNReal.continuous_coe.continuousAt.comp_continuousWithinAt hmean
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      exact ((Real.continuous_exp.continuousAt.comp_continuousWithinAt
        hmeanReal.neg).mul (hmeanReal.pow pending)).div_const _
    _ ≤ liminf (fun q : NNReal =>
        ∫⁻ v, (ProbabilityTheory.poissonMeasure (v.2 / q)) {pending} ∂mu)
        (𝓝[{q : NNReal | q ≠ 0}] r) := by
      apply lintegral_liminf_le
      intro q
      exact (Measure.measurable_coe (measurableSet_singleton pending)).comp
        (measurable_poissonMeasure.comp (measurable_snd.div measurable_const))

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · Fatou lower semicontinuity off zero, then singleton gluing
* this round · reduced · isolated the arbitrary-measure Poisson singleton coefficient
-/
