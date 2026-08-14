import Ttc.Exec.FiniteContinuingRetryExpectedCost
import Ttc.Exec.CVGaussianAugmentedSelectiveTV
import Ttc.Exec.RawGaussianLazyStoppedExecution

/-! Reference-law expected query bound for the augmented Gaussian retry phase. -/

namespace Ttc.CVGaussianAugmentedExpectedCost

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.FiniteContinuingRetry Ttc.FiniteContinuingRetryGaussian
open Ttc.FiniteContinuingRetryExpectedCost
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVCombinedContinuingRetryPhaseTV
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Exact operational accounting: accumulated traced membership queries equal the sum of
candidate-round query means over the unnormalised surviving-current laws. -/
theorem augmentedRetryQueryMean_eq_sum_running
    {K : Set (State n)} (hK : MeasurableSet K) (delta s c : Real)
    (hdelta : 0 < delta) (hc : c ≠ 0) (steps : Nat → Nat)
    (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho] (L : Nat) :
    (∫⁻ z, accumulatedCost z
      ∂(augmentedMarginalOf K hK delta s c hdelta hc steps rho L)) =
      ∑ j ∈ Finset.range L,
        ∫⁻ x, candidateMean (phaseCandidate K hK delta s hdelta steps)
          roundQueryCost j x
          ∂(runningCurrent
            (augmentedMarginalOf K hK delta s c hdelta hc steps rho j)) := by
  exact lintegral_accumulatedCost_embeddedMarginal
    (phaseCandidate K hK delta s hdelta steps)
    (costedCombinedAccept K c s) (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
    (by intro a; rfl) rho L

/-- A reference-law bound for each stopped-raw candidate round. -/
theorem six_mul_referenceCandidateMean_le_ten_mul_adjustable
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {q delta sigma R : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (pi : Measure (State n)) [IsProbabilityMeasure pi]
    (hpi : pi = ellGaussianProb K delta (sigma ^ 2))
    (t : Nat) :
    6 * (∫⁻ x, candidateMean
        (phaseCandidate K hK delta (sigma ^ 2) hdelta (fun _ ↦ t))
        roundQueryCost 0 x ∂pi) ≤ 10 * (t : ENNReal) := by
  have hmean : (∫⁻ x, candidateMean
        (phaseCandidate K hK delta (sigma ^ 2) hdelta (fun _ ↦ t))
        roundQueryCost 0 x ∂pi) =
      ∫⁻ omega, Ttc.RawGaussianLazyStoppedExecution.actualMembershipQueryCount t omega
        ∂Ttc.RawGaussianLazyStoppedExecution.lazyRawStoppedExecution
          K hK delta (sigma ^ 2) hdelta pi := by
    calc
      _ = ∫⁻ x, (∫⁻ omega,
          Ttc.RawGaussianLazyStoppedExecution.actualMembershipQueryCount t omega
          ∂Ttc.RawGaussianLazyStoppedExecution.lazyRawStoppedExecution
            K hK delta (sigma ^ 2) hdelta (Measure.dirac x)) ∂pi := by
        apply lintegral_congr
        intro x
        unfold candidateMean phaseCandidate roundQueryCost
        exact lintegral_fst_combinedRoundCostedKernel hK delta (sigma ^ 2) hdelta t x
      _ = _ := Ttc.CostedStatefulSpeedyPhases.lintegral_diracPhaseCost_eq_execution
        hK delta (sigma ^ 2) hdelta t pi
  rw [hmean]
  have hraw :=
    Ttc.RawGaussianLazyStoppedExecution.six_mul_expected_actualMembershipQueryCount_le_ten_mul_adjustable
      hn hK hKc hball hq hdelta hsigma hdeltan hdeltaq hR hRsigma hKR
      (mu := pi) (M := (1 : ENNReal)) (by simpa only [hpi] using
        (IsWarm.refl (ellGaussianProb K delta (sigma ^ 2)))) t
  simpa using hraw

/-- Polynomial retry-cost envelope.  Crucially the warm factor is paid once per retry;
it does not compound across retries because the surviving law is unnormalised. -/
theorem six_mul_augmentedRetryQueryMean_le_ten_sum
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    {q delta sigma R c : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hc : c ≠ 0)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (steps : Nat → Nat) (rho : Measure (ScoreSeed n)) [IsProbabilityMeasure rho]
    (pi : Measure (State n)) [IsProbabilityMeasure pi]
    (hpi : pi = ellGaussianProb K delta (sigma ^ 2))
    (M : ENNReal) (L : Nat)
    (hwarm : ∀ j, j < L → IsWarm M
      (runningCurrent
        (augmentedMarginalOf K hK delta (sigma ^ 2) c hdelta hc steps rho j)) pi) :
    6 * (∫⁻ z, accumulatedCost z
      ∂(augmentedMarginalOf K hK delta (sigma ^ 2) c hdelta hc steps rho L)) ≤
      ∑ j ∈ Finset.range L, 10 * ((steps j : ENNReal) * M) := by
  have hbase := lintegral_accumulatedCost_embeddedMarginal_le
    (phaseCandidate K hK delta (sigma ^ 2) hdelta steps)
    (costedCombinedAccept K c (sigma ^ 2))
    (measurableSet_costedCombinedAccept hK hc)
    rejectedNext measurable_rejectedNext
    (augmentedAcceptedOutput c) (measurable_augmentedAcceptedOutput c)
    roundQueryCost measurable_roundQueryCost augmentedEmbedding measurable_augmentedEmbedding
    (by intro a; rfl) rho L pi M hwarm
  calc
    6 * (∫⁻ z, accumulatedCost z
        ∂(augmentedMarginalOf K hK delta (sigma ^ 2) c hdelta hc steps rho L)) ≤
        6 * (∑ j ∈ Finset.range L, M *
          ∫⁻ x, candidateMean (phaseCandidate K hK delta (sigma ^ 2) hdelta steps)
            roundQueryCost j x ∂pi) := mul_le_mul_left' hbase 6
    _ = ∑ j ∈ Finset.range L, 6 * (M *
          ∫⁻ x, candidateMean (phaseCandidate K hK delta (sigma ^ 2) hdelta steps)
            roundQueryCost j x ∂pi) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range L, 10 * ((steps j : ENNReal) * M) := by
      apply Finset.sum_le_sum
      intro j hj
      have href := six_mul_referenceCandidateMean_le_ten_mul_adjustable
        hn hK hKc hball hq hdelta hsigma hdeltan hdeltaq hR hRsigma hKR pi hpi (steps j)
      have heq : (∫⁻ x, candidateMean
          (phaseCandidate K hK delta (sigma ^ 2) hdelta steps) roundQueryCost j x ∂pi) =
          ∫⁻ x, candidateMean
            (phaseCandidate K hK delta (sigma ^ 2) hdelta (fun _ ↦ steps j))
            roundQueryCost 0 x ∂pi := by
        apply lintegral_congr
        intro x
        rfl
      rw [heq]
      calc
        6 * (M * _) = M * (6 * _) := by ac_rfl
        _ ≤ M * (10 * (steps j : ENNReal)) := mul_le_mul_left' href M
        _ = 10 * ((steps j : ENNReal) * M) := by ac_rfl

#print axioms augmentedRetryQueryMean_eq_sum_running
#print axioms six_mul_augmentedRetryQueryMean_le_ten_sum

end Ttc.CVGaussianAugmentedExpectedCost
