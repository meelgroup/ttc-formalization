import Ttc.Exec.FiniteContinuingRetryGaussianAugmentedPhase
import Ttc.Exec.CostedTVTimeoutTransfer
import Arlib.Probability.TVKernelHeterogeneous

/-! Deterministic query cutoff for the augmented Gaussian retry phase. -/

namespace Ttc.AugmentedGaussianPhaseCutoff

open MeasureTheory ProbabilityTheory
open Arlib
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CostedTVTimeoutTransfer
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev AugmentedState (n : Nat) := State n × State n

noncomputable def cutoffCostOutput (fallback : AugmentedState n) (L : ENNReal)
    (z : RetryState (State n) (AugmentedState n)) : ENNReal × AugmentedState n :=
  (min (accumulatedCost z) L,
    cutoffOutput fallback L accumulatedCost output z)

theorem measurable_cutoffCostOutput (fallback : AugmentedState n) (L : ENNReal) :
    Measurable (cutoffCostOutput fallback L :
      RetryState (State n) (AugmentedState n) → ENNReal × AugmentedState n) := by
  apply Measurable.prodMk
  · exact measurable_accumulatedCost.min measurable_const
  · exact measurable_cutoffOutput fallback L measurable_accumulatedCost measurable_output

noncomputable def augmentedGaussianCutoffPhaseCostedKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (attempts : Nat) (cutoff : ENNReal) :
    Kernel (AugmentedState n) (ENNReal × AugmentedState n) :=
  Kernel.map
    (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps attempts)
    (cutoffCostOutput (0, 0) cutoff)

instance augmentedGaussianCutoffPhaseCostedKernel.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (attempts : Nat) (cutoff : ENNReal) :
    IsMarkovKernel
      (augmentedGaussianCutoffPhaseCostedKernel K hK delta s c hdelta hc steps
        attempts cutoff) := by
  unfold augmentedGaussianCutoffPhaseCostedKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_cutoffCostOutput (n := n) (0, 0) cutoff)

theorem stepMean_augmentedGaussianCutoffPhaseCostedKernel_le
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (attempts : Nat) (cutoff : ENNReal) (a : AugmentedState n) :
    Ttc.SequentialCost.stepMean
      (fun _ ↦ augmentedGaussianCutoffPhaseCostedKernel
        K hK delta s c hdelta hc steps attempts cutoff) 0 a ≤ cutoff := by
  unfold Ttc.SequentialCost.stepMean augmentedGaussianCutoffPhaseCostedKernel
  rw [Kernel.map_apply _ (measurable_cutoffCostOutput (n := n) (0, 0) cutoff),
    lintegral_map measurable_fst
      (measurable_cutoffCostOutput (n := n) (0, 0) cutoff)]
  calc
    (∫⁻ z, min (accumulatedCost z) cutoff
      ∂augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps attempts a) ≤
        ∫⁻ _z, cutoff
          ∂augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps attempts a :=
      lintegral_mono (fun z ↦ min_le_right _ _)
    _ = cutoff := by simp

/-- The cutoff output loses at most `B/cutoff + eps`, where `B` is the retry-query mean
under a nearby reference incoming law and `eps` is the incoming-law TV error. -/
theorem tvLe_cutoffPhase_of_reference
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (attempts : Nat) {rho nu : Measure (AugmentedState n)}
    [IsProbabilityMeasure rho] [IsProbabilityMeasure nu]
    {eps B cutoff : ENNReal} (hrho : TVLe rho nu eps)
    (hcut0 : cutoff ≠ 0) (hcuttop : cutoff ≠ ⊤)
    (href : augmentedPhaseQueryMean K hK delta s c hdelta hc steps attempts nu ≤ B) :
    TVLe
      (Measure.map
        (cutoffOutput (0, 0) cutoff accumulatedCost output)
        (sampleFromKernel
          (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps attempts) rho))
      (Measure.map output
        (sampleFromKernel
          (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps attempts) rho))
      (B / cutoff + eps) := by
  let R := augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps attempts
  have hout : TVLe (sampleFromKernel R rho) (sampleFromKernel R nu) eps := by
    unfold sampleFromKernel
    exact hrho.bind_kernel R
  apply tvLe_map_cutoffOutput_of_reference hout measurable_accumulatedCost
    measurable_output (0, 0) hcut0 hcuttop
  exact href

#print axioms stepMean_augmentedGaussianCutoffPhaseCostedKernel_le
#print axioms tvLe_cutoffPhase_of_reference

end Ttc.AugmentedGaussianPhaseCutoff
