import Ttc.Exec.CVScorePreservingSeedReset
import Ttc.Exec.CVIndependentRefreshSeedLaws
import Ttc.Exec.CVColdOperationalKernel
import Ttc.Exec.CVColdOperationalResetTV

/-!
# Concrete independently refreshed operational cold kernel

The score and accumulated membership-query count are produced by the existing zero-safe
cold phase.  Before storing the phase state, the raw seed is independently replaced by a
sample from the next phase's explicit Gaussian ball.  Thus actual-path seed warmth is an
exact marginal statement, independent of the retry outcome.
-/

set_option autoImplicit false

namespace Ttc.CVColdOperationalSeedReset

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVColdOperationalKernel
open Ttc.CVColdOperationalResetTV
open Ttc.CVScorePreservingSeedReset
open Ttc.CVIndependentRefreshSeedLaws
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVContinuingRetryParameters
open scoped ENNReal Classical BigOperators

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Unified refresh radius.  Early in the cold block it tracks the ambient Gaussian
scale; later it is capped at the fixed inner radius `1/4`. -/
noncomputable def coldNextRefreshRadius (n : Nat) (s : Real) : Real :=
  min hotRefreshRadius (coldRefreshRadius n s)

theorem coldNextRefreshRadius_pos
    (hn : 1 ≤ n) {s : Real} (hs : 0 < s) :
    0 < coldNextRefreshRadius n s := by
  unfold coldNextRefreshRadius
  exact lt_min hotRefreshRadius_pos (coldRefreshRadius_pos hn hs)

theorem coldNextRefreshRadius_lt_standardShrink
    (hn : 1 ≤ n) (s : Real) :
    coldNextRefreshRadius n s < 1 - 1 / (2 * (n : Real)) := by
  exact (min_le_left _ _).trans_lt (hotRefreshRadius_lt_standardShrink hn)

/-- Directly sampleable raw-seed law used after cold phase `i`, parameterized at the next
variance because it will initialize phase `i+1`. -/
noncomputable def coldNextRefreshSeed
    (n : Nat) (s0 : Real) (i : Nat) : Measure (State n) :=
  let snext := fixedSigmaSq n s0 (i + 1)
  coldBallStart (n := n) snext (coldNextRefreshRadius n snext)

/-- Exact finite warmness factor of the unified refresh against the next radius-four
body. -/
noncomputable def coldNextRefreshWarmFactor
    (n : Nat) (K : Set (State n)) (s0 : Real) (i : Nat) : ENNReal :=
  let snext := fixedSigmaSq n s0 (i + 1)
  gaussianBallWarmFactor (fixedRadiusFourBody K snext) snext
    (coldNextRefreshRadius n snext)

theorem isProbabilityMeasure_coldNextRefreshSeed
    (hn : 1 ≤ n) (s0 : Real) (hs0 : 0 < s0) (i : Nat) :
    IsProbabilityMeasure (coldNextRefreshSeed n s0 i) := by
  let snext := fixedSigmaSq n s0 (i + 1)
  have hsnext : 0 < snext := by
    dsimp only [snext]
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  unfold coldNextRefreshSeed
  exact isProbabilityMeasure_gaussianBallRefresh hsnext
    (coldNextRefreshRadius_pos hn hsnext)

/-- Score-preserving, independently refreshed uncosted cold phase. -/
noncomputable def coldGaussianResetKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    Kernel (State n) (ScoreSeed n) :=
  letI : IsProbabilityMeasure (coldNextRefreshSeed n s0 i) :=
    isProbabilityMeasure_coldNextRefreshSeed hn s0 hs0 i
  scoreSeedResetKernel
    (coldGaussianKernel hn K hK s0 hs0 retrySteps retries i)
    (coldNextRefreshSeed n s0 i)

instance coldGaussianResetKernel.isMarkovKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    IsMarkovKernel
      (coldGaussianResetKernel hn K hK s0 hs0 retrySteps retries i) := by
  unfold coldGaussianResetKernel
  infer_instance

/-- Costed refinement of `coldGaussianResetKernel`. -/
noncomputable def coldGaussianResetCostedKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    Kernel (State n) (ENNReal × ScoreSeed n) :=
  letI : IsProbabilityMeasure (coldNextRefreshSeed n s0 i) :=
    isProbabilityMeasure_coldNextRefreshSeed hn s0 hs0 i
  costedScoreSeedResetKernel
    (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i)
    (coldNextRefreshSeed n s0 i)

instance coldGaussianResetCostedKernel.isMarkovKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat) :
    IsMarkovKernel
      (coldGaussianResetCostedKernel hn K hK s0 hs0 retrySteps retries i) := by
  unfold coldGaussianResetCostedKernel
  infer_instance

/-- Exact pointwise erasure of the reset cost refinement. -/
theorem map_snd_coldGaussianResetCostedKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (coldGaussianResetCostedKernel hn K hK s0 hs0 retrySteps retries i x) =
      coldGaussianResetKernel hn K hK s0 hs0 retrySteps retries i x := by
  letI : IsProbabilityMeasure (coldNextRefreshSeed n s0 i) :=
    isProbabilityMeasure_coldNextRefreshSeed hn s0 hs0 i
  unfold coldGaussianResetCostedKernel coldGaussianResetKernel
  apply map_snd_costedScoreSeedResetKernel
  intro y
  exact map_snd_coldGaussianCostedKernel
    hn K hK s0 hs0 retrySteps retries i y

/-- Every incoming probability law produces exactly the declared fresh seed marginal. -/
theorem map_snd_sampleFrom_coldGaussianResetKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (rho : Measure (State n)) [IsProbabilityMeasure rho] :
    Measure.map Prod.snd
        (sampleFromKernel
          (coldGaussianResetKernel hn K hK s0 hs0 retrySteps retries i) rho) =
      coldNextRefreshSeed n s0 i := by
  letI : IsProbabilityMeasure (coldNextRefreshSeed n s0 i) :=
    isProbabilityMeasure_coldNextRefreshSeed hn s0 hs0 i
  unfold coldGaussianResetKernel
  exact map_snd_sampleFrom_scoreSeedResetKernel
    (coldGaussianKernel hn K hK s0 hs0 retrySteps retries i) rho
      (coldNextRefreshSeed n s0 i)

/-- The whole actual outgoing seed marginal is warm for the next radius-four speedy
target with an explicit Gaussian-normalizer ratio.  No premise about the incoming law's
warmth is needed for this conclusion. -/
theorem isWarm_seed_sampleFrom_coldGaussianResetKernel_next
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (hradNext : 1 ≤
      4 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n) :
    IsWarm (coldNextRefreshWarmFactor n K s0 i)
      (Measure.map Prod.snd
        (sampleFromKernel
          (coldGaussianResetKernel hn K hK s0 hs0 retrySteps retries i) rho))
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1)))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 (i + 1)))
        (fixedSigmaSq n s0 (i + 1))) := by
  rw [map_snd_sampleFrom_coldGaussianResetKernel]
  let snext := fixedSigmaSq n s0 (i + 1)
  let c : Real := 1 - 1 / (2 * (n : Real))
  let bodyNext := fixedRadiusFourBody K snext
  have hsnext : 0 < snext := by
    dsimp only [snext]
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hradius : 0 < coldNextRefreshRadius n snext :=
    coldNextRefreshRadius_pos hn hsnext
  have hradiusc : coldNextRefreshRadius n snext < c := by
    simpa only [c] using coldNextRefreshRadius_lt_standardShrink hn snext
  have hc0 : 0 < c := hradius.trans hradiusc
  have hc1 : c < 1 := by
    dsimp only [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hbodyM : MeasurableSet bodyNext := measurableSet_fixedRadiusFourBody hK _
  have hbodyC : Convex Real bodyNext := convex_fixedRadiusFourBody hKc _
  have hbodyBall : ball (0 : State n) 1 ⊆ bodyNext :=
    unitBall_subset_inter_closedBall hball (by simpa only [snext] using hradNext)
  have hbodyTop : volume bodyNext ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hdelta : 0 < fixedRadiusFourDelta n snext :=
    fixedRadiusFourDelta_pos hn hsnext
  have hdc : fixedRadiusFourDelta n snext ≤ 1 - c := by
    rw [show 1 - c = 1 / (2 * (n : Real)) by dsimp [c]; ring]
    exact fixedRadiusFourDelta_le_n
  simpa only [coldNextRefreshSeed, coldNextRefreshWarmFactor, snext, c, bodyNext] using
    (isWarm_gaussianBallRefresh_ellGaussianProb hbodyM hbodyC hbodyBall hbodyTop
      hsnext hradius hc0 hc1 hradiusc hdelta hdc)

/-- The next-seed warmness factor is finite, so its logarithm is a legitimate mixing
deadline input. -/
theorem coldNextRefreshWarmFactor_ne_top
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0) (i : Nat) :
    coldNextRefreshWarmFactor n K s0 i ≠ ⊤ := by
  let snext := fixedSigmaSq n s0 (i + 1)
  have hsnext : 0 < snext := by
    dsimp only [snext]
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  simpa only [coldNextRefreshWarmFactor, snext] using
    (gaussianBallWarmFactor_ne_top
      (measurableSet_fixedRadiusFourBody hK snext)
      (volume_inter_closedBall_ne_top K _) hsnext
      (coldNextRefreshRadius_pos hn hsnext))

/-- Full score/seed accuracy of the refreshed cold kernel.  The target is the exact
product of the truncated cooling score law and the independently sampled next seed; the
refresh spends no additional TV error. -/
theorem tvLe_coldGaussianResetKernel_score_prod_nextSeed_adjustable_zeroSafe_of_eq
    (hn : 21 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (hi : i < m)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    {M eta zeta : ENNReal} (hM1 : 1 ≤ M) (hMtop : M ≠ ⊤)
    (heta0 : eta ≠ 0) (hetatop : eta ≠ ⊤) (heta1 : eta ≤ 1)
    (hzeta0 : zeta ≠ 0) (hzetatop : zeta ≠ ⊤)
    (hzeta16 : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)))
    (L : Nat)
    (hsteps : retrySteps i = fun _ ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i) (M / eta) zeta)
    (hretries : retries i = L) :
    TVLe
      (sampleFromKernel
        (coldGaussianResetKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i) rho)
      ((coolLaw m (fixedSigmaSq n s0)
        (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i).prod
          (coldNextRefreshSeed n s0 i))
      (32 * zeta + (eta + continuingContraction ^ L)) := by
  have hn1 : 1 ≤ n := by omega
  letI : IsProbabilityMeasure (coldNextRefreshSeed n s0 i) :=
    isProbabilityMeasure_coldNextRefreshSeed hn1 s0 hs0 i
  have hprod :=
    tvLe_coldGaussian_score_prod_resetSeed_adjustable_zeroSafe_of_eq
      (m := m) hn K hK hKc hball s0 hs0 retrySteps retries i hi rho
      (coldNextRefreshSeed n s0 i) hM1 hMtop heta0 hetatop heta1
      hzeta0 hzetatop hzeta16 hrad hwarm L hsteps hretries
  unfold coldGaussianResetKernel
  rw [sampleFrom_scoreSeedResetKernel_eq_prod]
  exact hprod

/-- Independent seed refresh does not change the phase's expected membership-query cost. -/
theorem heterogeneousStepMean_coldGaussianResetCostedKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (i : Nat) (x : State n) :
    heterogeneousStepMean
        (coldGaussianResetCostedKernel hn K hK s0 hs0 retrySteps retries i) x =
      heterogeneousStepMean
        (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i) x := by
  letI : IsProbabilityMeasure (coldNextRefreshSeed n s0 i) :=
    isProbabilityMeasure_coldNextRefreshSeed hn s0 hs0 i
  unfold coldGaussianResetCostedKernel
  exact heterogeneousStepMean_costedScoreSeedResetKernel
    (coldGaussianCostedKernel hn K hK s0 hs0 retrySteps retries i)
      (coldNextRefreshSeed n s0 i) x

/-- The reset adds no membership-query cost, so the existing cold expected-cost envelope
applies verbatim. -/
theorem coldGaussianReset_referenceCost_le_of_warm
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
        (coldGaussianResetCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i) x ∂rho) ≤
      ∑ j ∈ Finset.range (retries i),
        10 * ((retrySteps i j : ENNReal) * M) := by
  simp_rw [heterogeneousStepMean_coldGaussianResetCostedKernel]
  exact coldGaussian_referenceCost_le_of_warm hn K hK hKc hball
    s0 hs0 retrySteps retries rho M i hrad hwarm

#print axioms map_snd_coldGaussianResetCostedKernel
#print axioms isWarm_seed_sampleFrom_coldGaussianResetKernel_next
#print axioms coldNextRefreshWarmFactor_ne_top
#print axioms tvLe_coldGaussianResetKernel_score_prod_nextSeed_adjustable_zeroSafe_of_eq
#print axioms heterogeneousStepMean_coldGaussianResetCostedKernel
#print axioms coldGaussianReset_referenceCost_le_of_warm

end Ttc.CVColdOperationalSeedReset
