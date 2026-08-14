import Ttc.Exec.FiniteContinuingRetryGaussianPhaseKernel
import Ttc.Exec.CVSourceOneRunFromCostedPhases

/-! Sequential phase schedules built from finite continuing Gaussian retries. -/

namespace Ttc.CVFiniteContinuingPhaseSchedule

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.Probability Arlib.MarkovChains
open Ttc.FiniteContinuingRetryGaussianPhaseKernel
open Ttc.CVSourceOneRunFromCostedPhases
open scoped ENNReal Classical Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Operational, cost-recording cutoff phase family. -/
noncomputable def finiteRetryCostedSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (fallback : Nat → State n)
    (retries : Nat → Nat) (queryCutoff : Nat → ENNReal) :
    Nat → Kernel (State n) (ENNReal × State n) :=
  fun i => gaussianCutoffPhaseCostedKernel K hK (delta i) (sigmaSq i) (shrink i)
    (hdelta i) (hshrink i) (retrySteps i) (fallback i) (retries i) (queryCutoff i)

instance finiteRetryCostedSchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (fallback : Nat → State n)
    (retries : Nat → Nat) (queryCutoff : Nat → ENNReal) (i : Nat) :
    IsMarkovKernel (finiteRetryCostedSchedule K hK delta sigmaSq shrink hdelta
      hshrink retrySteps fallback retries queryCutoff i) := by
  unfold finiteRetryCostedSchedule
  infer_instance

/-- Declared state schedule is definitionally the cost-erasure of the operational one. -/
noncomputable def finiteRetryStateSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (fallback : Nat → State n)
    (retries : Nat → Nat) (queryCutoff : Nat → ENNReal) :
    Nat → Kernel (State n) (State n) :=
  fun i => Kernel.map
    (finiteRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
      retrySteps fallback retries queryCutoff i) Prod.snd

instance finiteRetryStateSchedule.isMarkovKernel
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (fallback : Nat → State n)
    (retries : Nat → Nat) (queryCutoff : Nat → ENNReal) (i : Nat) :
    IsMarkovKernel (finiteRetryStateSchedule K hK delta sigmaSq shrink hdelta
      hshrink retrySteps fallback retries queryCutoff i) := by
  unfold finiteRetryStateSchedule
  exact Kernel.IsMarkovKernel.map _ measurable_snd

theorem map_snd_finiteRetryCostedSchedule
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (fallback : Nat → State n)
    (retries : Nat → Nat) (queryCutoff : Nat → ENNReal) (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (finiteRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps fallback retries queryCutoff i x) =
      finiteRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps fallback retries queryCutoff i x := by
  unfold finiteRetryStateSchedule
  rw [Kernel.map_apply _ measurable_snd]

/-- Every cutoff phase has a pointwise conditional mean at most its explicit budget. -/
theorem stepMean_finiteRetryCostedSchedule_le
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (fallback : Nat → State n)
    (retries : Nat → Nat) (queryCutoff : Nat → ENNReal) (i : Nat) (x : State n) :
    Ttc.SequentialCost.stepMean
      (finiteRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps fallback retries queryCutoff) i x ≤ queryCutoff i := by
  simpa only [finiteRetryCostedSchedule, Ttc.SequentialCost.stepMean] using
    (stepMean_gaussianCutoffPhaseCostedKernel_le hK
      (delta i) (sigmaSq i) (shrink i) (hdelta i) (hshrink i)
      (retrySteps i) (fallback i) x (retries i) (queryCutoff i))

/-- The cutoff schedule supplies the complete operational refinement interface with no
remaining cost hypothesis. -/
theorem finiteRetryCostedPhaseRefinement
    (K : Set (State n)) (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (fallback : Nat → State n)
    (retries : Nat → Nat) (queryCutoff : Nat → ENNReal)
    (mu0 : Measure (State n)) [IsProbabilityMeasure mu0] (m : Nat) :
    CostedPhaseKernelRefinement
      (finiteRetryStateSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps fallback retries queryCutoff)
      (finiteRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps fallback retries queryCutoff)
      mu0 m queryCutoff := by
  refine
    { forgetCost := map_snd_finiteRetryCostedSchedule K hK delta sigmaSq shrink
        hdelta hshrink retrySteps fallback retries queryCutoff
      phaseMean := ?_ }
  intro i hi
  letI : IsProbabilityMeasure
      (costedPhaseStateMarginal
        (finiteRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps fallback retries queryCutoff) mu0 i) := by
    unfold costedPhaseStateMarginal costedPhaseOneRunLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_snd.comp (measurable_pi_apply i)).aemeasurable
  calc
    (∫⁻ x, Ttc.SequentialCost.stepMean
      (finiteRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
        retrySteps fallback retries queryCutoff) i x
      ∂costedPhaseStateMarginal
        (finiteRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
          retrySteps fallback retries queryCutoff) mu0 i) ≤
        ∫⁻ _, queryCutoff i
          ∂costedPhaseStateMarginal
            (finiteRetryCostedSchedule K hK delta sigmaSq shrink hdelta hshrink
              retrySteps fallback retries queryCutoff) mu0 i :=
      lintegral_mono (stepMean_finiteRetryCostedSchedule_le K hK delta sigmaSq shrink
        hdelta hshrink retrySteps fallback retries queryCutoff i)
    _ = queryCutoff i := by simp

#print axioms map_snd_finiteRetryCostedSchedule
#print axioms stepMean_finiteRetryCostedSchedule_le
#print axioms finiteRetryCostedPhaseRefinement

end Ttc.CVFiniteContinuingPhaseSchedule
