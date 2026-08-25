import Kr25Ssmxt.Analysis.ComponentMemHasIndex
import Kr25Ssmxt.Analysis.ProcessComponentsEstimateAemeasurable
import Kr25Ssmxt.Analysis.ProcessComponentsIsProbabilityMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace Kr25Ssmxt

/--
The TTC measure-level control flow preserves total probability under the two oracle
contracts. This isolates normalization of all maps, binds, Poisson draws, and thinning
streams from the estimator's concentration argument.

INTERNAL: probability-law bookkeeping for the TTC estimator.
-/
lemma ttc_volume_accuracy_probability_measure
    {n k : Nat}
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (O : TTCOracles n k)
    (hvolume : ComputeVolumeContract O F hbounded params)
    (hsamples : GenerateSamplesContract O F hbounded params) :
    MeasureTheory.IsProbabilityMeasure (ttc F hbounded params O) := by
  let D := O.preprocessing.run F hbounded
  by_cases hD : D.componentCount = 0
  · rw [show ttc F hbounded params O = MeasureTheory.Measure.dirac 0 by
      simp [ttc, D, hD]]
    infer_instance
  · let b := (O.preprocessing.choosePrecision D params).value
    have hvolume' : ∀ P ∈ List.ofFn D.component,
        MeasureTheory.IsProbabilityMeasure
          (O.computeVolume P params.epsilonPrime (params.deltaPrime D.componentCount)) := by
      intro P hP
      obtain ⟨i, rfl⟩ := component_mem_has_index D hP
      exact (hvolume i).1
    have hsamples' : ∀ P ∈ List.ofFn D.component, ∀ count,
        MeasureTheory.IsProbabilityMeasure
          (O.generateSamples P count b params.epsilonPrime
            (params.deltaPrime D.componentCount)) := by
      intro P hP count
      obtain ⟨i, rfl⟩ := component_mem_has_index D hP
      exact (hsamples i count).1
    let core := processComponents O b params.epsilonPrime
      (params.deltaPrime D.componentCount) (params.threshold D.componentCount)
      (List.ofFn D.component) (TTCState.initial n)
    letI : MeasureTheory.IsProbabilityMeasure core :=
      processComponents_isProbabilityMeasure O b params.epsilonPrime
        (params.deltaPrime D.componentCount) (params.threshold D.componentCount)
        (List.ofFn D.component) hvolume' hsamples' (TTCState.initial n)
    have hestimate : AEMeasurable TTCState.estimate core :=
      processComponents_estimate_aemeasurable O b params.epsilonPrime
        (params.deltaPrime D.componentCount) (params.threshold D.componentCount)
        (List.ofFn D.component) (TTCState.initial n)
    rw [show ttc F hbounded params O = core.map TTCState.estimate by
      simp [ttc, D, hD, b, core]]
    exact MeasureTheory.Measure.isProbabilityMeasure_map hestimate

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · reduced · closed the target from list-fold normalization and reachable-state
  estimator measurability; proved the component-list/index bridge
-/
