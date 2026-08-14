import Ttc.Exec.CVSourceTruncatedFixedCost
import Ttc.Exec.CVCorrectedFixedBlockCost
import Ttc.Exec.CVGaussianScoreSeedPhaseKernel
import Ttc.Exec.CVGaussianAugmentedExpectedCost
import Ttc.Exec.CVGaussianWarmFallbackAnalytic
import Ttc.Exec.CVHeterogeneousHistoryReference
import Ttc.Exec.CVScoreSeedExceptionalCost

/-!
# Operational Gaussian kernel for the source cold block

The source cold block changes both its radius-four truncation and its speedy-walk step
size from phase to phase.  Consequently it cannot be represented by a single fixed-body
Gaussian schedule.  This file gives the literal phase-indexed costed kernel and proves
the interfaces used by the heterogeneous retained-history reference:

* exact erasure of the recorded membership-query cost;
* a seed-marginal TV bridge from the pair-valued finite-retry theorem; and
* exact law-level cost accounting, followed by the radius-four expected-query bound.

The final cost theorem deliberately retains the `runningCurrent` warmth hypothesis of
`six_mul_augmentedRetryQueryMean_le_ten_sum`.  Establishing that hypothesis for the
truncated cold reference is a separate analytic recurrence; it is not implied by TV
closeness to the untruncated cooling law.
-/

set_option autoImplicit false

namespace Ttc.CVColdOperationalKernel

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.FiniteContinuingRetry
open Ttc.FiniteContinuingRetryGaussianAugmentedPhase
open Ttc.CVGaussianAugmentedSelectiveTV
open Ttc.CVGaussianAugmentedExpectedCost
open Ttc.CVGaussianWarmFallbackAnalytic
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVCorrectedFixedBlockCost
open Ttc.FiniteContinuingRetryExpectedCost
open Ttc.CVHybridSchedule
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- The literal source cold-phase costed kernel.  Both the truncation and the speedy
step size depend on `i`; the input is the retained raw seed. -/
noncomputable def coldGaussianCostedKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    Kernel (State n) (ENNReal × ScoreSeed n) :=
  gaussianScoreSeedCostedKernel
    (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
    (measurableSet_fixedRadiusFourBody hK _)
    (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
    (fixedSigmaSq n s0 i)
    (1 - 1 / (2 * (n : Real)))
    (fixedRadiusFourDelta_pos hn (by
      unfold fixedSigmaSq
      exact geomSchedule_pos hs0 (by positivity) i))
    (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
    (retrySteps i) (retries i)

instance coldGaussianCostedKernel.isMarkovKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    IsMarkovKernel
      (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i) := by
  unfold coldGaussianCostedKernel
  infer_instance

/-- Cost-erased cold phase. -/
noncomputable def coldGaussianKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    Kernel (State n) (ScoreSeed n) :=
  Kernel.map (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i) Prod.snd

instance coldGaussianKernel.isMarkovKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    IsMarkovKernel (coldGaussianKernel hn K hK s0 hs0 retrySteps retries i) := by
  unfold coldGaussianKernel
  exact Kernel.IsMarkovKernel.map _ measurable_snd

/-- Exact pointwise cost erasure. -/
theorem map_snd_coldGaussianCostedKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i x) =
      coldGaussianKernel hn K hK s0 hs0 retrySteps retries i x := by
  rw [coldGaussianKernel, Kernel.map_apply _ measurable_snd]

/-- Law of the cost-erased cold phase from an arbitrary incoming seed law. -/
theorem sampleFrom_coldGaussianKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (i : Nat) :
    sampleFromKernel
        (coldGaussianKernel hn K hK s0 hs0 retrySteps retries i) rho =
      Measure.map output
        (augmentedMarginalOf
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
          (measurableSet_fixedRadiusFourBody hK _)
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i)
          (1 - 1 / (2 * (n : Real)))
          (fixedRadiusFourDelta_pos hn (by
            unfold fixedSigmaSq
            exact geomSchedule_pos hs0 (by positivity) i))
          (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
          (retrySteps i)
          (Measure.map
            (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho)
          (retries i)) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  let rhoPair := Measure.map (seedEmbedding c) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  unfold coldGaussianKernel coldGaussianCostedKernel
  rw [Ttc.CVFiniteContinuingPhaseDistributional.sampleFromKernel_map _ Prod.snd
    measurable_snd rho]
  unfold gaussianScoreSeedCostedKernel sampleFromKernel
  rw [Arlib.MarkovChains.bind_comap]
  change Measure.map Prod.snd
      (sampleFromKernel
        (augmentedGaussianFinitePhaseCostedKernel
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
          (measurableSet_fixedRadiusFourBody hK _)
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i) c
          (fixedRadiusFourDelta_pos hn (by
            unfold fixedSigmaSq
            exact geomSchedule_pos hs0 (by positivity) i))
          (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
          (retrySteps i) (retries i)) rhoPair) = _
  unfold augmentedGaussianFinitePhaseCostedKernel
  rw [Ttc.CVFiniteContinuingPhaseDistributional.sampleFromKernel_map _
    augmentedPhaseCostOutput measurable_augmentedPhaseCostOutput rhoPair,
    Measure.map_map measurable_snd measurable_augmentedPhaseCostOutput]
  change Measure.map output
      (sampleFromKernel
        (augmentedGaussianRetryStateKernel
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
          (measurableSet_fixedRadiusFourBody hK _)
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i) c
          (fixedRadiusFourDelta_pos hn (by
            unfold fixedSigmaSq
            exact geomSchedule_pos hs0 (by positivity) i))
          (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
          (retrySteps i) (retries i)) rhoPair) = _
  rw [sampleFrom_augmentedRetryStateKernel_eq_marginalOf]

/-- Pair-valued finite-retry accuracy immediately gives the exact seed-marginal premise
used by the heterogeneous retained-history reference. -/
theorem tvLe_seed_bind_coldGaussianCostedKernel_of_pair
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (i : Nat)
    (mu : Measure (State n)) {eps : ENNReal}
    (hpair : TVLe
      (sampleFromKernel
        (coldGaussianKernel hn K hK s0 hs0 retrySteps retries i) rho)
      (scoreSeedReference (1 - 1 / (2 * (n : Real))) mu) eps) :
    TVLe
      (rho.bind (Kernel.map
        (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
      (Measure.map
        (fun y : State n ↦ (1 - 1 / (2 * (n : Real))) • y) mu) eps := by
  have herase :
      rho.bind (Kernel.map
        (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i)
          (fun y : ENNReal × ScoreSeed n ↦ y.2.2)) =
        Measure.map Prod.snd
          (sampleFromKernel
            (coldGaussianKernel hn K hK s0 hs0 retrySteps retries i) rho) := by
    change sampleFromKernel
        (Kernel.map
          (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i)
          (fun y : ENNReal × ScoreSeed n ↦ y.2.2)) rho =
      Measure.map Prod.snd
        (sampleFromKernel
          (Kernel.map
            (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i)
            Prod.snd) rho)
    rw [Ttc.CVFiniteContinuingPhaseDistributional.sampleFromKernel_map _
      (fun y : ENNReal × ScoreSeed n ↦ y.2.2) (by fun_prop) rho]
    rw [Ttc.CVFiniteContinuingPhaseDistributional.sampleFromKernel_map _ Prod.snd
      measurable_snd rho]
    rw [Measure.map_map measurable_snd measurable_snd]
    rfl
  rw [herase]
  exact Ttc.CVScoreSeedExceptionalCost.tvLe_seed_of_scoreSeedReference hpair

/-- Exact `hphaseSeedTV` shape: identify the scaled score reference with the declared
next seed target after applying the pair-valued finite-retry theorem. -/
theorem tvLe_seed_bind_coldGaussianCostedKernel_of_pair_target
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (i : Nat)
    (mu tauNext : Measure (State n)) {eps : ENNReal}
    (hpair : TVLe
      (sampleFromKernel
        (coldGaussianKernel hn K hK s0 hs0 retrySteps retries i) rho)
      (scoreSeedReference (1 - 1 / (2 * (n : Real))) mu) eps)
    (htarget : Measure.map
      (fun y : State n ↦ (1 - 1 / (2 * (n : Real))) • y) mu = tauNext) :
    TVLe
      (rho.bind (Kernel.map
        (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
      tauNext eps := by
  rw [← htarget]
  exact tvLe_seed_bind_coldGaussianCostedKernel_of_pair
    hn K hK s0 hs0 retrySteps retries rho i mu hpair

/-- Exact identification of the heterogeneous phase mean with the augmented retry
query mean under the embedded incoming reference seed law. -/
theorem lintegral_heterogeneousStepMean_coldGaussianCostedKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho] (i : Nat) :
    (∫⁻ x, heterogeneousStepMean
        (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i) x ∂rho) =
      augmentedPhaseQueryMean
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (measurableSet_fixedRadiusFourBody hK _)
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)
        (1 - 1 / (2 * (n : Real)))
        (fixedRadiusFourDelta_pos hn (by
          unfold fixedSigmaSq
          exact geomSchedule_pos hs0 (by positivity) i))
        (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
        (retrySteps i) (retries i)
        (Measure.map
          (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hs : 0 < fixedSigmaSq n s0 i := by
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) i
  let hdelta : 0 < fixedRadiusFourDelta n (fixedSigmaSq n s0 i) :=
    fixedRadiusFourDelta_pos hn hs
  let rhoPair := Measure.map (seedEmbedding c) rho
  letI : IsProbabilityMeasure rhoPair :=
    Measure.isProbabilityMeasure_map (measurable_seedEmbedding c).aemeasurable
  let Q := augmentedGaussianFinitePhaseCostedKernel
    (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
    (measurableSet_fixedRadiusFourBody hK _)
    (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
    (fixedSigmaSq n s0 i) c hdelta
    (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
    (retrySteps i) (retries i)
  have hQmean : Measurable (fun a ↦ ∫⁻ y, y.1 ∂Q a) :=
    measurable_fst.lintegral_kernel
  change (∫⁻ x, ∫⁻ y, y.1 ∂Q (seedEmbedding c x) ∂rho) = _
  rw [← lintegral_map hQmean (measurable_seedEmbedding c)]
  simpa only [rhoPair, Q, Ttc.SequentialCost.stepMean] using
    (lintegral_stepMean_augmentedGaussianFinitePhaseCostedKernel
      (measurableSet_fixedRadiusFourBody hK _)
      (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
      (fixedSigmaSq n s0 i) c hdelta
      (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
      (retrySteps i) (retries i) rhoPair)

/-- Killed-current induction for the literal cold phase.  No new retry-by-retry premise
is needed: an `M`-warm incoming seed remains `M`-warm on every unnormalised surviving
branch because rejected transitions are subkernels of the truncated stationary law. -/
theorem isWarm_runningCurrent_coldGaussian
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0) (retrySteps : Nat → Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (i : Nat) {M : ENNReal}
    [IsProbabilityMeasure (ellGaussianProb
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
      (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
      (fixedSigmaSq n s0 i))]
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i))) : ∀ j,
    IsWarm M
      (Ttc.FiniteContinuingRetryExpectedCost.runningCurrent
        (augmentedMarginalOf
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
          (measurableSet_fixedRadiusFourBody hK _)
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i)
          (1 - 1 / (2 * (n : Real)))
          (fixedRadiusFourDelta_pos hn (by
            unfold fixedSigmaSq
            exact geomSchedule_pos hs0 (by positivity) i))
          (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
          (retrySteps i)
          (Measure.map
            (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) j))
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)) := by
  intro j
  exact isWarm_runningCurrent_augmentedMarginalOf_gaussian
    (measurableSet_fixedRadiusFourBody hK _)
    (fixedRadiusFourDelta_pos hn (by
      unfold fixedSigmaSq
      exact geomSchedule_pos hs0 (by positivity) i))
    (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero hn)
    rho hwarm (retrySteps i) j

/-- Radius-four specialization of the augmented retry-cost theorem.  This is the
per-phase `hphaseCost` input required by the heterogeneous retained-history reference.
The only non-geometric premise left visible is warmth of each unnormalised surviving
current law against the exact truncated speedy stationary law. -/
theorem six_mul_coldGaussian_referenceCost_le
    (hn : 2 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (pi : Measure (State n)) [IsProbabilityMeasure pi]
    (M : ENNReal) (i : Nat)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hpi : pi = ellGaussianProb
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
      (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
      (fixedSigmaSq n s0 i))
    (hwarm : ∀ j, j < retries i → IsWarm M
      (runningCurrent
        (augmentedMarginalOf
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
          (measurableSet_fixedRadiusFourBody hK _)
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i)
          (1 - 1 / (2 * (n : Real)))
          (fixedRadiusFourDelta_pos (by omega : 1 ≤ n) (by
            unfold fixedSigmaSq
            exact geomSchedule_pos hs0 (by positivity) i))
          (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero (by omega : 1 ≤ n))
          (retrySteps i)
          (Measure.map
            (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) j)) pi) :
    6 * (∫⁻ x, heterogeneousStepMean
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i) x ∂rho) ≤
      ∑ j ∈ Finset.range (retries i),
        10 * ((retrySteps i j : ENNReal) * M) := by
  have hs : 0 < fixedSigmaSq n s0 i := by
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) i
  have hsqrt : 0 < Real.sqrt (fixedSigmaSq n s0 i) := Real.sqrt_pos.2 hs
  have hsquare : Real.sqrt (fixedSigmaSq n s0 i) ^ 2 =
      fixedSigmaSq n s0 i := Real.sq_sqrt hs.le
  letI : IsProbabilityMeasure
      (Measure.map (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) :=
    Measure.isProbabilityMeasure_map
      (measurable_seedEmbedding (1 - 1 / (2 * (n : Real)))).aemeasurable
  rw [lintegral_heterogeneousStepMean_coldGaussianCostedKernel
    (by omega : 1 ≤ n) K hK s0 hs0 retrySteps retries rho i]
  unfold augmentedPhaseQueryMean
  rw [sampleFrom_augmentedRetryStateKernel_eq_marginalOf]
  simpa only [hsquare] using
    (six_mul_augmentedRetryQueryMean_le_ten_sum
    (q := 4) (sigma := Real.sqrt (fixedSigmaSq n s0 i))
    (R := 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    hn (measurableSet_fixedRadiusFourBody hK _)
    (convex_fixedRadiusFourBody hKc _)
    (Arlib.MarkovChains.unitBall_subset_inter_closedBall hball hrad)
    (by norm_num) (fixedRadiusFourDelta_pos (by omega : 1 ≤ n) hs)
    hsqrt (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero (by omega : 1 ≤ n))
    fixedRadiusFourDelta_le_n
    (by
      simpa only [max_eq_left (by norm_num : (8 : Real) ≥ 2 * 4)] using
        (fixedRadiusFourDelta_le_radius
          (n := n) (s := fixedSigmaSq n s0 i)))
    (by positivity) le_rfl
    (fun x hx ↦ norm_le_fixedRadiusFour hx)
    (retrySteps i)
    (Measure.map
      (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho)
    pi
    (by simpa only [hsquare] using hpi)
    M (retries i)
    (by simpa only [hsquare] using hwarm))

/-- Direct (slightly looser) `hphaseCost` form of the preceding radius-four bound. -/
theorem coldGaussian_referenceCost_le
    (hn : 2 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (pi : Measure (State n)) [IsProbabilityMeasure pi]
    (M : ENNReal) (i : Nat)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hpi : pi = ellGaussianProb
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
      (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
      (fixedSigmaSq n s0 i))
    (hwarm : ∀ j, j < retries i → IsWarm M
      (runningCurrent
        (augmentedMarginalOf
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
          (measurableSet_fixedRadiusFourBody hK _)
          (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
          (fixedSigmaSq n s0 i)
          (1 - 1 / (2 * (n : Real)))
          (fixedRadiusFourDelta_pos (by omega : 1 ≤ n) (by
            unfold fixedSigmaSq
            exact geomSchedule_pos hs0 (by positivity) i))
          (Ttc.CVScoreSeedExceptionalCost.standardShrink_ne_zero (by omega : 1 ≤ n))
          (retrySteps i)
          (Measure.map
            (seedEmbedding (1 - 1 / (2 * (n : Real)))) rho) j)) pi) :
    (∫⁻ x, heterogeneousStepMean
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i) x ∂rho) ≤
      ∑ j ∈ Finset.range (retries i),
        10 * ((retrySteps i j : ENNReal) * M) := by
  let A := ∫⁻ x, heterogeneousStepMean
    (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
      retrySteps retries i) x ∂rho
  let B := ∑ j ∈ Finset.range (retries i),
    10 * ((retrySteps i j : ENNReal) * M)
  have hsix : 6 * A ≤ B := six_mul_coldGaussian_referenceCost_le
    hn K hK hKc hball s0 hs0 retrySteps retries rho pi M i hrad hpi hwarm
  exact (calc
    A = 1 * A := by rw [one_mul]
    _ ≤ 6 * A := by gcongr <;> norm_num
    _ ≤ B := hsix)

/-- Strongest premise-minimal cold reference-cost theorem.  The retry-wise warmth
assumption has been discharged by killed-submeasure induction; only warmth of the phase's
incoming exact reference seed remains. -/
theorem coldGaussian_referenceCost_le_of_warm
    (hn : 2 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (M : ENNReal) (i : Nat)
    [IsProbabilityMeasure (ellGaussianProb
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
      (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
      (fixedSigmaSq n s0 i))]
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i))) :
    (∫⁻ x, heterogeneousStepMean
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i) x ∂rho) ≤
      ∑ j ∈ Finset.range (retries i),
        10 * ((retrySteps i j : ENNReal) * M) := by
  apply coldGaussian_referenceCost_le hn K hK hKc hball s0 hs0
    retrySteps retries rho
    (ellGaussianProb
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
      (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
      (fixedSigmaSq n s0 i)) M i hrad rfl
  intro j _hj
  exact isWarm_runningCurrent_coldGaussian (by omega : 1 ≤ n)
    K hK s0 hs0 retrySteps rho i hwarm j

/-- In particular, an exact truncated-speedy reference seed pays the cost envelope with
warmness one.  This is the binder-free reference-law specialization used when a history
reset chooses the phase stationary law itself. -/
theorem coldGaussian_stationaryReferenceCost_le
    (hn : 2 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat)
    [IsProbabilityMeasure (ellGaussianProb
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
      (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
      (fixedSigmaSq n s0 i))]
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n) :
    (∫⁻ x, heterogeneousStepMean
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i) x
      ∂(ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i))) ≤
      ∑ j ∈ Finset.range (retries i),
        10 * (retrySteps i j : ENNReal) := by
  simpa using coldGaussian_referenceCost_le_of_warm hn K hK hKc hball
    s0 hs0 retrySteps retries
    (ellGaussianProb
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
      (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
      (fixedSigmaSq n s0 i)) 1 i hrad (IsWarm.refl _)

#print axioms map_snd_coldGaussianCostedKernel
#print axioms sampleFrom_coldGaussianKernel
#print axioms tvLe_seed_bind_coldGaussianCostedKernel_of_pair
#print axioms tvLe_seed_bind_coldGaussianCostedKernel_of_pair_target
#print axioms lintegral_heterogeneousStepMean_coldGaussianCostedKernel
#print axioms isWarm_runningCurrent_coldGaussian
#print axioms six_mul_coldGaussian_referenceCost_le
#print axioms coldGaussian_referenceCost_le
#print axioms coldGaussian_referenceCost_le_of_warm
#print axioms coldGaussian_stationaryReferenceCost_le

end Ttc.CVColdOperationalKernel
