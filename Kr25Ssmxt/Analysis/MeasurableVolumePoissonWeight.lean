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
outcome law is measurable in the sampling rate.

INTERNAL: coefficient obtained by expanding the volume and Poisson binds into a
countable sum; its proof uses lower semicontinuity away from rate zero and a
measurable singleton split at zero.
-/
lemma measurable_volume_poisson_weight
    (mu : MeasureTheory.Measure VolumeOutcome) (pending : Nat) :
    Measurable (fun r : NNReal =>
      ∫⁻ v, (ProbabilityTheory.poissonMeasure (v.2 * r)) {pending} ∂mu) := by
  apply LowerSemicontinuous.measurable
  rw [lowerSemicontinuous_iff_le_liminf]
  intro r
  calc
    (∫⁻ v, (ProbabilityTheory.poissonMeasure (v.2 * r)) {pending} ∂mu) =
        ∫⁻ v, liminf (fun q : NNReal =>
          (ProbabilityTheory.poissonMeasure (v.2 * q)) {pending})
          (𝓝 r) ∂mu := by
      congr 1 with v
      apply Eq.symm
      apply Filter.Tendsto.liminf_eq
      simp_rw [ProbabilityTheory.poissonMeasure_singleton]
      have hmean : ContinuousAt (fun q : NNReal => v.2 * q) r :=
        continuousAt_const.mul continuousAt_id
      have hmeanReal : ContinuousAt
          (fun q : NNReal => ((v.2 * q : NNReal) : Real)) r :=
        NNReal.continuous_coe.continuousAt.comp hmean
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      exact ((Real.continuous_exp.continuousAt.comp
        hmeanReal.neg).mul (hmeanReal.pow pending)).div_const _
    _ ≤ liminf (fun q : NNReal =>
        ∫⁻ v, (ProbabilityTheory.poissonMeasure (v.2 * q)) {pending} ∂mu)
        (𝓝 r) := by
      apply lintegral_liminf_le
      intro q
      exact (Measure.measurable_coe (measurableSet_singleton pending)).comp
        (measurable_poissonMeasure.comp (measurable_snd.mul measurable_const))

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · Fatou lower semicontinuity off zero, then singleton gluing
* this round · reduced · isolated the arbitrary-measure Poisson singleton coefficient
-/
