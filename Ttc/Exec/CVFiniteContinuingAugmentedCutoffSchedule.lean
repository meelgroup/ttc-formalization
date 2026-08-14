import Ttc.Exec.AugmentedGaussianPhaseCutoff
import Ttc.Exec.GenericCostedPhaseCertificate

/-! Polynomial-cost schedule seam for capped augmented Gaussian phases. -/

namespace Ttc.CVFiniteContinuingAugmentedCutoffSchedule

open MeasureTheory ProbabilityTheory Set
open Arlib.Probability
open Ttc.AugmentedGaussianPhaseCutoff
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.GenericCostedPhaseCertificate
open Ttc.CVSourcePolynomialCutoffCapstone
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev AugmentedState (n : Nat) := State n × State n

noncomputable def cutoffCostedSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (cutoff : Nat → ENNReal) :
    Nat → Kernel (AugmentedState n) (ENNReal × AugmentedState n) := fun i ↦
  augmentedGaussianCutoffPhaseCostedKernel K hK (delta i) (sigmaSq i) (shrink i)
    (hdelta i) (hshrink i) (retrySteps i) (retries i) (cutoff i)

instance cutoffCostedSchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (cutoff : Nat → ENNReal) (i : Nat) :
    IsMarkovKernel (cutoffCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries cutoff i) := by
  unfold cutoffCostedSchedule
  infer_instance

noncomputable def cutoffStateSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (cutoff : Nat → ENNReal) :
    Nat → Kernel (AugmentedState n) (AugmentedState n) := fun i ↦
  Kernel.map (cutoffCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
    retrySteps retries cutoff i) Prod.snd

instance cutoffStateSchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (cutoff : Nat → ENNReal) (i : Nat) :
    IsMarkovKernel (cutoffStateSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries cutoff i) := by
  unfold cutoffStateSchedule
  exact Kernel.IsMarkovKernel.map _ measurable_snd

theorem stepMean_cutoffCostedSchedule_le
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (cutoff : Nat → ENNReal) (i : Nat) (a : AugmentedState n) :
    Ttc.SequentialCost.stepMean
      (cutoffCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries cutoff) i a ≤ cutoff i := by
  unfold Ttc.SequentialCost.stepMean cutoffCostedSchedule
  unfold augmentedGaussianCutoffPhaseCostedKernel
  rw [Kernel.map_apply _
      (measurable_cutoffCostOutput (n := n) (0, 0) (cutoff i)),
    lintegral_map measurable_fst
      (measurable_cutoffCostOutput (n := n) (0, 0) (cutoff i))]
  calc
    (∫⁻ z, min (Ttc.FiniteContinuingRetry.accumulatedCost z) (cutoff i)
      ∂augmentedGaussianRetryStateKernel K hK (delta i) (sigmaSq i) (shrink i)
        (hdelta i) (hshrink i) (retrySteps i) (retries i) a) ≤
      ∫⁻ _z, cutoff i
        ∂augmentedGaussianRetryStateKernel K hK (delta i) (sigmaSq i) (shrink i)
          (hdelta i) (hshrink i) (retrySteps i) (retries i) a :=
        lintegral_mono (fun z ↦ min_le_right _ _)
    _ = cutoff i := by simp

/-- No analytic cost premise remains: every phase records at most its deterministic
cutoff, so the expected one-run query count is bounded by the sum of cutoffs. -/
theorem cutoffRefinement
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (cutoff : Nat → ENNReal) (mu0 : Measure (AugmentedState n))
    [IsProbabilityMeasure mu0] (m : Nat) :
    Refinement
      (cutoffStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries cutoff)
      (cutoffCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries cutoff) mu0 m cutoff where
  forgetCost := by
    intro i a
    unfold cutoffStateSchedule
    rw [Kernel.map_apply _ measurable_snd]
  phaseMean := by
    intro i hi
    let rho := stateMarginal
      (cutoffCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps retries cutoff) mu0 i
    letI : IsProbabilityMeasure rho := by
      dsimp only [rho, stateMarginal, oneRunLaw]
      letI : IsProbabilityMeasure
          (Ttc.SequentialCost.execution
            (cutoffCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps retries cutoff) mu0) := inferInstance
      exact Measure.isProbabilityMeasure_map
        (measurable_snd.comp (measurable_pi_apply i)).aemeasurable
    calc
      (∫⁻ a, Ttc.SequentialCost.stepMean
          (cutoffCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
            retrySteps retries cutoff) i a
        ∂rho) ≤ ∫⁻ _a, cutoff i ∂rho := by
        apply lintegral_mono
        intro a
        exact stepMean_cutoffCostedSchedule_le K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries cutoff i a
      _ = cutoff i := by simp

/-- Direct adapter to the source cutoff/median capstone.  Its only non-cost premise is
accuracy of the capped augmented state path; the query bound is the explicit cutoff sum. -/
theorem sourceOneRunCertificate_of_cutoffSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (cutoff : Nat → ENNReal) (mu0 : Measure (AugmentedState n))
    [IsProbabilityMeasure mu0] (m : Nat)
    (est : StatePath (AugmentedState n) → Real) (hest : Measurable est)
    {runtimeConstant R eps lo hi : Real}
    (hsum : (∑ i ∈ Finset.range m, cutoff i) ≤
      sourceOneRunQueryBudget runtimeConstant n R eps)
    (haccuracy : 4 / 5 ≤
      (inhomogeneousPathMeasure
        (cutoffStateSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries cutoff) mu0).real {omega | est omega ∈ Icc lo hi}) :
    SourceOneRunCertificate
      (oneRunLaw
        (cutoffCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps retries cutoff) mu0)
      (queryCost m) (value est) runtimeConstant n R eps lo hi := by
  exact sourceOneRunCertificate_of_refinement
    (cutoffStateSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries cutoff)
    (cutoffCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries cutoff) mu0 m cutoff
    (cutoffRefinement K hK delta sigmaSq shrink hdelta hshrink
      retrySteps retries cutoff mu0 m) est hest hsum haccuracy

#print axioms cutoffRefinement
#print axioms sourceOneRunCertificate_of_cutoffSchedule

end Ttc.CVFiniteContinuingAugmentedCutoffSchedule
