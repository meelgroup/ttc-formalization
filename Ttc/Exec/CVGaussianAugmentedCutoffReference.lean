import Ttc.Exec.CVGaussianAugmentedExpectedCost
import Ttc.Exec.AugmentedGaussianPhaseCutoff

/-! Query-timeout transfer for the augmented Gaussian phase under an exact reference law. -/

namespace Ttc.CVGaussianAugmentedCutoffReference

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.FiniteContinuingRetry Ttc.FiniteContinuingRetryExpectedCost
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianAugmentedExpectedCost
open Ttc.AugmentedGaussianPhaseCutoff
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Coarse division-free form of the adjustable query estimate, directly suitable for
Markov timeout. -/
theorem augmentedPhaseQueryMean_le_ten_sum
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {q delta sigma R c : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hc : c ≠ 0)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (steps : Nat → Nat) (nu : Measure (ScoreSeed n)) [IsProbabilityMeasure nu]
    (pi : Measure (State n)) [IsProbabilityMeasure pi]
    (hpi : pi = ellGaussianProb K delta (sigma ^ 2))
    (M : ENNReal) (attempts : Nat)
    (hwarm : ∀ j, j < attempts → IsWarm M
      (runningCurrent
        (augmentedMarginalOf K hK delta (sigma ^ 2) c hdelta hc steps nu j)) pi) :
    augmentedPhaseQueryMean K hK delta (sigma ^ 2) c hdelta hc steps attempts nu ≤
      ∑ j ∈ Finset.range attempts, 10 * ((steps j : ENNReal) * M) := by
  have hsix := six_mul_augmentedRetryQueryMean_le_ten_sum
    hn hK hKc hball hq hdelta hsigma hc hdeltan hdeltaq hR hRsigma hKR
    steps nu pi hpi M attempts hwarm
  have heq : augmentedPhaseQueryMean K hK delta (sigma ^ 2) c hdelta hc
      steps attempts nu =
      ∫⁻ z, accumulatedCost z
        ∂(augmentedMarginalOf K hK delta (sigma ^ 2) c hdelta hc steps nu attempts) := by
    unfold augmentedPhaseQueryMean
    rw [sampleFrom_augmentedRetryStateKernel_eq_marginalOf hK delta
      (sigma ^ 2) c hdelta hc steps nu attempts]
  rw [heq]
  exact (calc
    (∫⁻ z, accumulatedCost z
      ∂(augmentedMarginalOf K hK delta (sigma ^ 2) c hdelta hc steps nu attempts)) ≤
        6 * (∫⁻ z, accumulatedCost z
          ∂(augmentedMarginalOf K hK delta (sigma ^ 2) c hdelta hc steps nu attempts)) := by
            exact (le_mul_of_one_le_left (by simp) (by norm_num : (1 : ENNReal) ≤ 6))
    _ ≤ _ := hsix)

/-- Capped execution versus the exact pair reference.  `phaseError` is supplied by the
uncapped selective theorem; timeout contributes only `B/cutoff + inputError`. -/
theorem tvLe_augmentedCutoffPhase_to_reference
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (attempts : Nat) {rho nu target : Measure (ScoreSeed n)}
    [IsProbabilityMeasure rho] [IsProbabilityMeasure nu]
    {inputError phaseError B cutoff : ENNReal}
    (hinput : TVLe rho nu inputError)
    (hcut0 : cutoff ≠ 0) (hcuttop : cutoff ≠ ⊤)
    (href : augmentedPhaseQueryMean K hK delta s c hdelta hc steps attempts nu ≤ B)
    (hphase : TVLe
      (Measure.map output
        (augmentedMarginalOf K hK delta s c hdelta hc steps rho attempts))
      target phaseError) :
    TVLe
      (Measure.map
        (Ttc.CostedTVTimeoutTransfer.cutoffOutput (0, 0) cutoff accumulatedCost output)
        (Ttc.CVSequentialPhaseSampler.sampleFromKernel
          (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps attempts) rho))
      target ((B / cutoff + inputError) + phaseError) := by
  have hcut := tvLe_cutoffPhase_of_reference hK delta s c hdelta hc steps attempts
    hinput hcut0 hcuttop href
  have hphase' : TVLe
      (Measure.map output
        (Ttc.CVSequentialPhaseSampler.sampleFromKernel
          (augmentedGaussianRetryStateKernel K hK delta s c hdelta hc steps attempts) rho))
      target phaseError := by
    rw [sampleFrom_augmentedRetryStateKernel_eq_marginalOf hK delta s c hdelta hc
      steps rho attempts]
    exact hphase
  exact hcut.trans hphase'

#print axioms augmentedPhaseQueryMean_le_ten_sum
#print axioms tvLe_augmentedCutoffPhase_to_reference

end Ttc.CVGaussianAugmentedCutoffReference
