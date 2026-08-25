import Kr25Ssmxt.Analysis.ProcessComponentIsProbabilityMeasure
import Kr25Ssmxt.Analysis.ProcessComponentsKernelMeasurable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Normalization of the TTC component fold

Sequentially binding normalized component steps preserves total probability.
-/

namespace Kr25Ssmxt

/--
A list of component steps is normalized when both oracle laws are normalized at every
component in the list.

INTERNAL: normalization bookkeeping for the recursive TTC component fold.
-/
lemma processComponents_isProbabilityMeasure {n k : Nat} (O : TTCOracles n k) (b : Nat)
    (epsilonPrime deltaPrime threshold : Real) (Ps : List (PolytopeData n))
    (hvolume : ∀ P ∈ Ps, MeasureTheory.IsProbabilityMeasure
      (O.computeVolume P epsilonPrime deltaPrime))
    (hsamples : ∀ P ∈ Ps, ∀ count, MeasureTheory.IsProbabilityMeasure
      (O.generateSamples P count b epsilonPrime deltaPrime))
    (state : TTCState n) :
    MeasureTheory.IsProbabilityMeasure
      (processComponents O b epsilonPrime deltaPrime threshold Ps state) := by
  induction Ps generalizing state with
  | nil =>
      simp only [processComponents]
      infer_instance
  | cons P rest ih =>
      simp only [processComponents]
      letI : MeasureTheory.IsProbabilityMeasure
          (processComponent O b epsilonPrime deltaPrime threshold P state) :=
        processComponent_isProbabilityMeasure O b epsilonPrime deltaPrime threshold P
          (hvolume P (by simp)) (fun count => hsamples P (by simp) count) state
      apply MeasureTheory.isProbabilityMeasure_bind
        (processComponents_kernel_measurable O b epsilonPrime deltaPrime threshold rest).aemeasurable
      filter_upwards with nextState
      exact ih
        (fun P' hP' => hvolume P' (by simp [hP']))
        (fun P' hP' count => hsamples P' (by simp [hP']) count)
        nextState

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · induction over the component list using one-step normalization and
  measurable tail kernels
-/
