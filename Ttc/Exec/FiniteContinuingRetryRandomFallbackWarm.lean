import Ttc.Exec.FiniteContinuingRetryRandomFallback
import Arlib.Probability.WarmMixture

/-! Warmness of the independent random fallback postprocessor. -/

namespace Ttc.FiniteContinuingRetryRandomFallbackWarm

open MeasureTheory ProbabilityTheory
open Arlib
open Ttc.CVSequentialPhaseSampler
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryRandomFallback
open scoped ENNReal

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- An accepted sublaw and an independent warm fallback combine additively.  The fallback
is multiplied by the unresolved survival probability, which is at most one, so its warm
constant is paid only once. -/
theorem isWarm_sampleFrom_randomFallbackKernel
    (mu : Measure (RetryState E F)) [IsProbabilityMeasure mu]
    (fallbackLaw target : Measure F) [IsProbabilityMeasure fallbackLaw]
    {Macc Mfallback : ENNReal}
    (haccepted : IsWarm Macc (acceptedOutputSubmeasure mu) target)
    (hfallback : IsWarm Mfallback fallbackLaw target) :
    IsWarm (Macc + Mfallback)
      (sampleFromKernel (randomFallbackKernel fallbackLaw) mu) target := by
  rw [sampleFrom_randomFallbackKernel mu fallbackLaw]
  apply haccepted.add
  have hscaled := hfallback.smul (mu Ttc.FiniteContinuingRetry.runningStates) Mfallback
  exact hscaled.mono <| by
    have hsurv : mu Ttc.FiniteContinuingRetry.runningStates ≤ 1 := prob_le_one
    simpa only [one_mul] using
      mul_le_mul_right' hsurv Mfallback

end Ttc.FiniteContinuingRetryRandomFallbackWarm

#print axioms Ttc.FiniteContinuingRetryRandomFallbackWarm.isWarm_sampleFrom_randomFallbackKernel
