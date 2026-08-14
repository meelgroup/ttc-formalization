import Ttc.Exec.CVSourceWeightedMeanRepair
import Ttc.Exec.CVColdHotReferenceCost
import Ttc.Exec.CVColdHotScoreSeedSchedule
import Ttc.Exec.CVColdOperationalKernel
import Ttc.Exec.CVColdOperationalPairTV
import Ttc.Exec.CVColdCrossPhaseWarm
import Ttc.Exec.CVColdOperationalTransition
import Ttc.Exec.CVColdOperationalSeedReset
import Ttc.Exec.CVColdOperationalFullTarget
import Ttc.Exec.CVScorePreservingSeedReset
import Ttc.Exec.CVProductStateCostReset
import Ttc.Exec.CVIndependentRefreshSeedLaws
import Ttc.Exec.CVHotRefreshRadialRuntime
import Ttc.Exec.CVHotRefreshDeadline
import Ttc.Exec.CVGaussianWarmFallbackCostedPhaseKernel
import Ttc.Exec.CVRadialLogEnvelope
import Ttc.Exec.CVFiniteAugmentedSeedOperational
import Ttc.Exec.CVRelativeWeightedRetainedCertificate

/-!
# Concrete Gaussian hybrid retained-history certificate

This file fixes both the uncosted and costed kernels to the finite-retry Gaussian
score/seed implementation.  The exact cost-erasure identity is discharged internally,
the initial history has zero cost, and the cold/hot source arithmetic supplies the
complete expected-query budget for twice the source estimator sample count.
-/

set_option autoImplicit false

namespace Ttc.CVGaussianHybridWeightedCertificate

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.CVFiniteAugmentedSeedOperational
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVHeterogeneousRetainedPathLaw
open Ttc.CVRetainedHistoryReferenceInduction
open Ttc.CVRelativeWeightedRetainedCertificate
open Ttc.CVColdHotReferenceCost
open Ttc.CVColdHotScoreSeedSchedule
open Ttc.CVColdOperationalKernel
open Ttc.CVColdOperationalPairTV
open Ttc.CVColdCrossPhaseWarm
open Ttc.CVColdOperationalTransition
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVCombinedContinuingAccept
open Ttc.CVContinuingRetryParameters
open Ttc.CVGaussianWarmFallbackOperational
open Ttc.CVGaussianWarmFallbackCostedPhaseKernel
open Ttc.CVRadialLogEnvelope
open Ttc.CVSourceReferenceTVCapstone
open Ttc.CVHybridSchedule
open Ttc.CVCorrected
open Ttc.CVRelativeMeanClippingAssembly
open Ttc.CVIndependentStreamMoments
open Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianScoreAwareMeanBudget
open Ttc.CVGaussianScoreAwareParameters
open Ttc.CVGaussianSourceWeightedMoment
open Ttc.CVSourceWeightedMeanRepair
open Arlib.GaussianCooling
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

theorem map_snd_initialHeterogeneousHistoryLaw
    (mu : Measure (State n × State n)) [SFinite mu] :
    Measure.map Prod.snd (initialHeterogeneousHistoryLaw mu) =
      Measure.map Prod.snd mu := by
  unfold initialHeterogeneousHistoryLaw
  rw [Measure.map_map measurable_snd measurable_initialHeterogeneousHistoryState]
  congr 1

theorem lintegral_initialHeterogeneousHistoryCost
    (mu : Measure (State n × State n)) :
    (∫⁻ z, z.1.1 ∂initialHeterogeneousHistoryLaw mu) = 0 := by
  unfold initialHeterogeneousHistoryLaw
  change (∫⁻ z, (Prod.fst ∘ Prod.fst) z
    ∂Measure.map initialHeterogeneousHistoryState mu) = 0
  rw [lintegral_map (measurable_fst.comp measurable_fst)
    measurable_initialHeterogeneousHistoryState]
  simp [initialHeterogeneousHistoryState]

/-! ## Operational cold reference bridge -/

/-- The exact seed reference emitted by an ideal radius-four cold phase.  This is the
reference used for retained-history TV and cost accounting; it deliberately retains the
truncated body, because replacing it by the full-body cooling law destroys the finite
warmness needed by the next cold walk. -/
noncomputable def coldAcceptedSeedTarget
    (n : Nat) (K : Set (State n)) (s0 : Real) (i : Nat) : Measure (State n) :=
  let s := fixedSigmaSq n s0 i
  let delta := fixedRadiusFourDelta n s
  let c : Real := 1 - 1 / (2 * (n : Real))
  Measure.map (fun y : State n ↦ c • y)
    (Measure.map (combinedOutput c)
      (Arlib.condOn
        (Ttc.SpeedyRejection.proposal
          (ellGaussianProb (fixedRadiusFourBody K s) delta s))
        (combinedAccept
          (fixedRadiusFourBody K s) c s)))

/-- Speedy stationary law used by the operational radius-four walk at cold phase `i`. -/
noncomputable def coldStationarySeed
    (n : Nat) (K : Set (State n)) (s0 : Real) (i : Nat) : Measure (State n) :=
  ellGaussianProb
    (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
    (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
    (fixedSigmaSq n s0 i)

/-- Explicit warmness constant transported between successive radius-four cold bodies. -/
noncomputable def coldCrossWarmFactor (n : Nat) : ENNReal :=
  ENNReal.ofReal
      ((1 - 1 / (2 * (n : Real)))⁻¹ ^ n) *
    (ENNReal.ofReal (Real.exp (1 / 2)) * 2)

theorem one_le_coldCrossWarmFactor (hn : 1 ≤ n) :
    1 ≤ coldCrossWarmFactor n := by
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hc0 : 0 < c := by
    dsimp [c]
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have : 0 ≤ 1 / (2 * (n : Real)) := by positivity
    linarith
  have hinv : 1 ≤ c⁻¹ := (one_le_inv₀ hc0).2 hc1
  have hp : 1 ≤ c⁻¹ ^ n := one_le_pow₀ hinv
  have he : (1 : Real) ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)
  unfold coldCrossWarmFactor
  change 1 ≤ ENNReal.ofReal (c⁻¹ ^ n) * (ENNReal.ofReal (Real.exp (1 / 2)) * 2)
  calc
    1 = 1 * 1 := by simp
    _ ≤ ENNReal.ofReal (c⁻¹ ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2) := by
      gcongr
      · exact ENNReal.one_le_ofReal.mpr hp
      · calc
          1 = 1 * 1 := by simp
          _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) * 2 := by
            gcongr
            exact ENNReal.one_le_ofReal.mpr he
            norm_num

theorem coldCrossWarmFactor_ne_top (n : Nat) : coldCrossWarmFactor n ≠ ⊤ := by
  unfold coldCrossWarmFactor
  apply ENNReal.mul_ne_top
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)

/-- The denotational accepted seed target is exactly the scaled, truncated cooling law.
This is the equality that makes the zero-safe operational TV theorem and the changing-body
cross-warm theorem talk about the same measure. -/
theorem coldAcceptedSeedTarget_eq_scaledTruncatedCoolLaw
    (hn : 1 ≤ n) {m : Nat} (K : Set (State n))
    (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (s0 : Real) (hs0 : 0 < s0) {i : Nat} (hi : i < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n) :
    coldAcceptedSeedTarget n K s0 i =
      Measure.map
        (fun y : State n ↦ (1 - 1 / (2 * (n : Real))) • y)
        (coolLaw m (fixedSigmaSq n s0)
          (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i) := by
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hbodyM : MeasurableSet
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) :=
    measurableSet_fixedRadiusFourBody hK _
  have hbodyC : Convex Real
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) :=
    convex_fixedRadiusFourBody hKc _
  have hbodyBall : ball (0 : State n) 1 ⊆
      fixedRadiusFourBody K (fixedSigmaSq n s0 i) :=
    Arlib.MarkovChains.unitBall_subset_inter_closedBall hball hrad
  have hbodyFin : volume
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) ≠ ⊤ :=
    Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
  have hs : 0 < fixedSigmaSq n s0 i := hsigma i
  have hideal :=
    Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
      hn hsigma hbodyM hbodyC hbodyBall hbodyFin
      (fixedRadiusFourDelta_pos hn hs)
      (fixedRadiusFourDelta_le_n (n := n)) hi
  unfold coldAcceptedSeedTarget
  dsimp only
  rw [hideal]

/-- Zero-safe finite-retry TV, with its target rewritten to the exact retained cold
reference.  All speedy mixing, acceptance, killed-current, and retry-survival facts are
already discharged by the underlying operational theorem. -/
theorem tvLe_seed_bind_coldGaussianCostedKernel_coldAcceptedSeedTarget
    (hn : 21 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0) (i : Nat)
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
    (L : Nat) :
    let deadline := fun W : ENNReal ↦
      Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i) W zeta
    let retrySteps : Nat → Nat → Nat := fun _ _ ↦ deadline (M / eta)
    let retries : Nat → Nat := fun _ ↦ L
    TVLe
      (rho.bind (Kernel.map
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i)
        (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
      (coldAcceptedSeedTarget n K s0 i)
      (32 * zeta + (eta + continuingContraction ^ L)) := by
  dsimp only
  simpa only [coldAcceptedSeedTarget] using
    (tvLe_seed_bind_coldGaussianCostedKernel_adjustable_zeroSafe
      hn K hK hKc hball s0 hs0 i rho hM1 hMtop heta0 hetatop heta1
      hzeta0 hzetatop hzeta16 hrad hwarm L)

/-- The exact retained cold target is warm for the next truncated speedy stationary
law, with no analytic premise left beyond the standard radius hypotheses. -/
theorem isWarm_coldAcceptedSeedTarget_succ
    (hn : 1 ≤ n) {m : Nat} (K : Set (State n))
    (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (s0 : Real) (hs0 : 0 < s0) {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n) :
    IsWarm (coldCrossWarmFactor n)
      (coldAcceptedSeedTarget n K s0 i)
      (coldStationarySeed n K s0 (i + 1)) := by
  unfold coldCrossWarmFactor coldStationarySeed
  rw [coldAcceptedSeedTarget_eq_scaledTruncatedCoolLaw hn K hK hKc hball hfin
    s0 hs0 (Nat.lt_of_succ_lt hi) hrad]
  exact isWarm_standardScaledTruncated_ellGaussianProb_succ
    (m := m) hn hs0 hK hKc hball hfin hi hrad hradTwo
      (fixedRadiusFourDelta_pos hn (by
        unfold fixedSigmaSq
        exact geomSchedule_pos hs0 (by positivity) (i + 1)))
      (fixedRadiusFourDelta_le_n (n := n))

/-- Cold-to-hot boundary: the final truncated cold target is warm for the next
full-body speedy stationary law.  This removes the support mismatch at the splice. -/
theorem isWarm_coldAcceptedSeedTarget_full_succ
    (hn : 1 ≤ n) {m : Nat} (K : Set (State n))
    (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (s0 : Real) (hs0 : 0 < s0) {i : Nat} (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    IsWarm (coldCrossWarmFactor n)
      (coldAcceptedSeedTarget n K s0 i)
      (ellGaussianProb K delta (fixedSigmaSq n s0 (i + 1))) := by
  rw [coldAcceptedSeedTarget_eq_scaledTruncatedCoolLaw hn K hK hKc hball hfin
    s0 hs0 (Nat.lt_of_succ_lt hi) hrad]
  simpa only [coldCrossWarmFactor] using
    (isWarm_standardScaledTruncated_full_ellGaussianProb_succ
      (m := m) hn hs0 hK hKc hball hfin hi hrad hradTwo hdelta hdeltan)

/-- The predecessor-target family automatically supplies the incoming warmth of every
active cold reference seed.  Only the initial seed warmth is external; all successors
are discharged by `isWarm_coldAcceptedSeedTarget_succ`. -/
theorem isWarm_coldRetainedReferenceFamily
    (hn : 1 ≤ n) {cold : Nat} (K : Set (State n))
    (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (s0 : Real) (hs0 : 0 < s0)
    (tauSeed : Nat → Measure (State n))
    (M0 : ENNReal)
    (hstart : IsWarm M0 (tauSeed 0) (coldStationarySeed n K s0 0))
    (htarget : ∀ i, i < cold →
      tauSeed (i + 1) = coldAcceptedSeedTarget n K s0 i)
    (hrad : ∀ i, i < cold →
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : ∀ i, i + 1 < cold →
      1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n) :
    ∀ i, i < cold →
      IsWarm (if i = 0 then M0 else coldCrossWarmFactor n)
        (tauSeed i) (coldStationarySeed n K s0 i) := by
  intro i hi
  cases i with
  | zero => simpa using hstart
  | succ j =>
      have hj : j < cold := by omega
      rw [if_neg (Nat.succ_ne_zero j), htarget j hj]
      exact isWarm_coldAcceptedSeedTarget_succ
        (m := cold + 1) hn K hK hKc hball hfin s0 hs0
        (by omega) (hrad j hj) (hradTwo j (by omega))

/-- Geometry-only wrapper for the cold expected-cost theorem.  In particular, callers
do not have to manufacture the probability-measure instance for the truncated speedy
stationary law. -/
theorem coldGaussian_referenceCost_le_of_geometry_warm
    (hn : 2 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (rho : Measure (State n)) [IsProbabilityMeasure rho]
    (M : ENNReal) (i : Nat)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hwarm : IsWarm M rho (coldStationarySeed n K s0 i)) :
    (∫⁻ x, heterogeneousStepMean
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i) x ∂rho) ≤
      ∑ j ∈ Finset.range (retries i),
        10 * ((retrySteps i j : ENNReal) * M) := by
  let body := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
  let delta := fixedRadiusFourDelta n (fixedSigmaSq n s0 i)
  let s := fixedSigmaSq n s0 i
  have hs : 0 < s := by
    dsimp only [s]
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) i
  have hbodyM : MeasurableSet body := measurableSet_fixedRadiusFourBody hK _
  have hbodyC : Convex Real body := convex_fixedRadiusFourBody hKc _
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    Arlib.MarkovChains.unitBall_subset_inter_closedBall hball hrad
  have hbodyTop : volume body ≠ ⊤ :=
    Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
  have hdelta : 0 < delta := fixedRadiusFourDelta_pos (by omega) hs
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    dsimp [c]
    have hn1 : 1 ≤ n := by omega
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn1
    have : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdeltaC : delta ≤ 1 - c := by
    dsimp only [delta, c]
    simpa using (fixedRadiusFourDelta_le_n
      (n := n) (s := fixedSigmaSq n s0 i))
  have hmass0 : ellGaussianMeasure body delta s Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hbodyM hbodyC hbodyBall
      hc0 hc1 hdelta hdeltaC hs
  have hmassTop : ellGaussianMeasure body delta s Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hs body delta hbodyTop
  letI : IsProbabilityMeasure (ellGaussianProb body delta s) :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmassTop
  apply coldGaussian_referenceCost_le_of_warm hn K hK hKc hball s0 hs0
    retrySteps retries rho M i
  · exact hrad
  · simpa only [coldStationarySeed, body, delta, s] using hwarm

/-- Phasewise warm budget of the retained cold reference: the caller chooses the
initial factor, and every successor uses the explicit changing-body factor. -/
noncomputable def coldReferenceWarmBudget
    (n : Nat) (M0 : ENNReal) (i : Nat) : ENNReal :=
  if i = 0 then M0 else coldCrossWarmFactor n

theorem one_le_coldReferenceWarmBudget
    (hn : 1 ≤ n) {M0 : ENNReal} (hM0 : 1 ≤ M0) (i : Nat) :
    1 ≤ coldReferenceWarmBudget n M0 i := by
  unfold coldReferenceWarmBudget
  split_ifs
  · exact hM0
  · exact one_le_coldCrossWarmFactor hn

theorem coldReferenceWarmBudget_ne_top
    {M0 : ENNReal} (hM0 : M0 ≠ ⊤) (n i : Nat) :
    coldReferenceWarmBudget n M0 i ≠ ⊤ := by
  unfold coldReferenceWarmBudget
  split_ifs
  · exact hM0
  · exact coldCrossWarmFactor_ne_top n

/-- Literal adjustable speedy deadline used by the zero-safe cold kernel. -/
noncomputable def coldAdjustableRetrySteps
    (n : Nat) (s0 : Real) (M eta zeta : Nat → ENNReal) : Nat → Nat → Nat :=
  fun i _ ↦ Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
    (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
    (fixedSigmaSq n s0 i) (M i / eta i) (zeta i)

/-- The exact per-phase seed-TV error of the adjustable zero-safe cold kernel. -/
noncomputable def coldAdjustablePhaseError
    (eta zeta : Nat → ENNReal) (L : Nat → Nat) (i : Nat) : ENNReal :=
  32 * zeta i + (eta i + continuingContraction ^ L i)

/-- Complete retained-reference interface for every cold phase.  Cross-phase warmth,
zero-safe seed TV, stationary probability, and expected kernel cost are discharged.
The remaining `hcostShape` premise is pure arithmetic converting the explicit retry
sum to the real-valued phase envelope used by the public runtime theorem. -/
theorem operationalColdRetainedPhaseTVAndCost
    (hn : 21 ≤ n) {cold : Nat} (K : Set (State n))
    (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (s0 : Real) (hs0 : 0 < s0)
    (tauSeed : Nat → Measure (State n)) [∀ i, IsProbabilityMeasure (tauSeed i)]
    (M0 : ENNReal)
    (hstart : IsWarm M0 (tauSeed 0) (coldStationarySeed n K s0 0))
    (htarget : ∀ i, i < cold →
      tauSeed (i + 1) = coldAcceptedSeedTarget n K s0 i)
    (hrad : ∀ i, i < cold →
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : ∀ i, i + 1 < cold →
      1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    (eta zeta : Nat → ENNReal) (L : Nat → Nat)
    (hM01 : 1 ≤ M0) (hM0top : M0 ≠ ⊤)
    (heta0 : ∀ i, i < cold → eta i ≠ 0)
    (hetatop : ∀ i, i < cold → eta i ≠ ⊤)
    (heta1 : ∀ i, i < cold → eta i ≤ 1)
    (hzeta0 : ∀ i, i < cold → zeta i ≠ 0)
    (hzetatop : ∀ i, i < cold → zeta i ≠ ⊤)
    (hzeta16 : ∀ i, i < cold → zeta i ≤ ENNReal.ofReal (1 / 16 : Real))
    (coldMean : Nat → Real)
    (hcostShape : ∀ i, i < cold →
      (∑ j ∈ Finset.range (L i),
        10 * ((((coldAdjustableRetrySteps n s0
          (coldReferenceWarmBudget n M0) eta zeta) i j : Nat) : ENNReal) *
            coldReferenceWarmBudget n M0 i)) ≤ ENNReal.ofReal (coldMean i)) :
    ∀ i, i < cold →
      TVLe
        ((tauSeed i).bind (Kernel.map
          (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
            (coldAdjustableRetrySteps n s0
              (coldReferenceWarmBudget n M0) eta zeta) L i)
          (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
        (tauSeed (i + 1)) (coldAdjustablePhaseError eta zeta L i) ∧
      (∫⁻ x, heterogeneousStepMean
          (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
            (coldAdjustableRetrySteps n s0
              (coldReferenceWarmBudget n M0) eta zeta) L i) x ∂tauSeed i) ≤
        ENNReal.ofReal (coldMean i) := by
  intro i hi
  have hwarm : IsWarm (coldReferenceWarmBudget n M0 i)
      (tauSeed i) (coldStationarySeed n K s0 i) := by
    simpa only [coldReferenceWarmBudget] using
      (isWarm_coldRetainedReferenceFamily (by omega : 1 ≤ n)
        K hK hKc hball hfin s0 hs0 tauSeed M0 hstart htarget hrad hradTwo i hi)
  constructor
  · rw [htarget i hi]
    rw [coldAcceptedSeedTarget_eq_scaledTruncatedCoolLaw
      (by omega : 1 ≤ n) K hK hKc hball hfin s0 hs0 hi (hrad i hi)]
    simpa [coldAdjustableRetrySteps, coldAdjustablePhaseError,
      coldIdealSeedReference] using
      (tvLe_seed_bind_coldGaussianCostedKernel_coldIdealSeedReference
        (m := cold) hn K hK hKc hball s0 hs0
        (coldAdjustableRetrySteps n s0
          (coldReferenceWarmBudget n M0) eta zeta) L i hi (tauSeed i)
        (one_le_coldReferenceWarmBudget (by omega : 1 ≤ n) hM01 i)
        (coldReferenceWarmBudget_ne_top hM0top n i)
        (heta0 i hi) (hetatop i hi) (heta1 i hi)
        (hzeta0 i hi) (hzetatop i hi) (hzeta16 i hi) (hrad i hi) hwarm (L i)
        rfl rfl)
  · exact (coldGaussian_referenceCost_le_of_geometry_warm
      (by omega : 2 ≤ n) K hK hKc hball s0 hs0
      (coldAdjustableRetrySteps n s0
        (coldReferenceWarmBudget n M0) eta zeta) L
      (tauSeed i) (coldReferenceWarmBudget n M0 i) i (hrad i hi) hwarm).trans
        (hcostShape i hi)

/-- Piecewise retained-reference interface with the cold block fully instantiated by
the operational radius-four kernel.  After this theorem, the only phase-law premises
are the hot kernel's seed TV and cost bounds; cold transition TV, cross warmth, and cost
are no longer exposed to the final source-sharp certificate. -/
theorem operationalColdHotRetainedPhaseTVAndCost
    (hn : 21 ≤ n) {cold hot : Nat}
    (K : Set (State n)) (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (s0 : Real) (hs0 : 0 < s0)
    (Qhot : Nat → Kernel (State n) (ENNReal × (State n × State n)))
    [∀ i, IsMarkovKernel (Qhot i)]
    (tauSeed : Nat → Measure (State n)) [∀ i, IsProbabilityMeasure (tauSeed i)]
    (e : Nat → ENNReal) (M0 : ENNReal)
    (hstart : IsWarm M0 (tauSeed 0) (coldStationarySeed n K s0 0))
    (htarget : ∀ i, i < cold →
      tauSeed (i + 1) = coldAcceptedSeedTarget n K s0 i)
    (hrad : ∀ i, i < cold →
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : ∀ i, i + 1 < cold →
      1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    (eta zeta : Nat → ENNReal) (L : Nat → Nat)
    (hM01 : 1 ≤ M0) (hM0top : M0 ≠ ⊤)
    (heta0 : ∀ i, i < cold → eta i ≠ 0)
    (hetatop : ∀ i, i < cold → eta i ≠ ⊤)
    (heta1 : ∀ i, i < cold → eta i ≤ 1)
    (hzeta0 : ∀ i, i < cold → zeta i ≠ 0)
    (hzetatop : ∀ i, i < cold → zeta i ≠ ⊤)
    (hzeta16 : ∀ i, i < cold → zeta i ≤ ENNReal.ofReal (1 / 16 : Real))
    (coldMean hotMean : Nat → Real)
    (hcostShape : ∀ i, i < cold →
      (∑ j ∈ Finset.range (L i),
        10 * ((((coldAdjustableRetrySteps n s0
          (coldReferenceWarmBudget n M0) eta zeta) i j : Nat) : ENNReal) *
            coldReferenceWarmBudget n M0 i)) ≤ ENNReal.ofReal (coldMean i))
    (hcoldError : ∀ i, i < cold →
      coldAdjustablePhaseError eta zeta L i ≤ e i)
    (hhotTV : ∀ j, j < hot →
      TVLe
        ((tauSeed (cold + j)).bind (Kernel.map (Qhot j)
          (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
        (tauSeed (cold + j + 1)) (e (cold + j)))
    (hhotCost : ∀ j, j < hot →
      (∫⁻ x, heterogeneousStepMean (Qhot j) x ∂tauSeed (cold + j)) ≤
        ENNReal.ofReal (hotMean j)) :
    (∀ i, i < cold + hot →
      TVLe
        ((tauSeed i).bind (Kernel.map
          (coldHotCostedSchedule cold
            (fun q ↦ coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
              (coldAdjustableRetrySteps n s0
                (coldReferenceWarmBudget n M0) eta zeta) L q)
            Qhot i)
          (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
        (tauSeed (i + 1)) (e i)) ∧
    (∀ i, i < cold + hot →
      (∫⁻ x, heterogeneousStepMean
        (coldHotCostedSchedule cold
          (fun q ↦ coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
            (coldAdjustableRetrySteps n s0
              (coldReferenceWarmBudget n M0) eta zeta) L q)
          Qhot i) x ∂tauSeed i) ≤
        coldHotPhaseMean cold hot coldMean hotMean i) := by
  have hcold := operationalColdRetainedPhaseTVAndCost hn K hK hKc hball hfin
    s0 hs0 tauSeed M0 hstart htarget hrad hradTwo eta zeta L hM01 hM0top
    heta0 hetatop heta1 hzeta0 hzetatop hzeta16 coldMean hcostShape
  constructor
  · intro i hi
    by_cases hicold : i < cold
    · have hphase := (hcold i hicold).1
      unfold coldHotCostedSchedule
      rw [dif_pos hicold]
      exact hphase.mono (hcoldError i hicold)
    · have hj : i - cold < hot := by omega
      have hieq : cold + (i - cold) = i := by omega
      unfold coldHotCostedSchedule
      rw [dif_neg hicold]
      simpa only [hieq, Nat.add_assoc] using hhotTV (i - cold) hj
  · intro i hi
    by_cases hicold : i < cold
    · have hphase := (hcold i hicold).2
      unfold coldHotCostedSchedule coldHotPhaseMean coldHotPhaseMeanReal
      rw [dif_pos hicold, if_pos hicold]
      exact hphase
    · have hj : i - cold < hot := by omega
      have hieq : cold + (i - cold) = i := by omega
      unfold coldHotCostedSchedule coldHotPhaseMean coldHotPhaseMeanReal
      rw [dif_neg hicold, if_neg hicold, if_pos hi]
      simpa only [hieq] using hhotCost (i - cold) hj

/-- Cost arithmetic for the literal weighted-accuracy choice `eps/100`.  The factor
`10000` is universal and is absorbed into the public runtime constant; no new
dimension, radius, or accuracy exponent is introduced. -/
theorem doubledEstimator_innerHundred_coldHotPhaseSum_le_sourceBudget
    {runtimeConstant radius eps : Real} {dim cold hot hotChunks : Nat}
    (hn : 1 ≤ dim) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (coldMean hotMean : Nat → Real)
    (hcold : ∀ i, 0 ≤ coldMean i) (hhot : ∀ i, 0 ≤ hotMean i)
    (hcoldHotShape :
      20000 * weightedSampleNumerator dim cold hotChunks *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i) ≤
        sourceOneRunQueryCore runtimeConstant dim radius eps) :
    let k := estimatorSamples dim cold hotChunks (eps / 100)
    (2 * k : ENNReal) * ∑ i ∈ Finset.range (cold + hot),
        coldHotPhaseMean cold hot coldMean hotMean i ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant dim radius eps := by
  dsimp only
  let k := estimatorSamples dim cold hotChunks (eps / 100)
  have hi0 : 0 < eps / 100 := by positivity
  have hi1 : eps / 100 ≤ 1 := by linarith
  have hk := estimatorSamples_cast_le_weighted_div_epsSq
    (cold := cold) (hotChunks := hotChunks) hn hi0 hi1
  have hsum0 : 0 ≤
      (∑ i ∈ Finset.range cold, coldMean i) +
        ∑ i ∈ Finset.range hot, hotMean i := by
    exact add_nonneg (Finset.sum_nonneg fun i _ ↦ hcold i)
      (Finset.sum_nonneg fun i _ ↦ hhot i)
  have hreal : (((2 * k : Nat) : Real) *
      ∑ i ∈ Finset.range (cold + hot),
        coldHotPhaseMeanReal cold hot coldMean hotMean i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryEnvelope
        runtimeConstant dim radius eps := by
    rw [sum_coldHotPhaseMeanReal]
    rw [sourceOneRunQueryEnvelope_eq_core_div]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hepsSq : 0 < eps ^ 2 := sq_pos_of_pos heps
    calc
      (2 : Real) * (k : Real) *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i) ≤
        2 * (weightedSampleNumerator dim cold hotChunks / (eps / 100) ^ 2) *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i) := by gcongr
      _ = (20000 * weightedSampleNumerator dim cold hotChunks *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i)) / eps ^ 2 := by
        field_simp [ne_of_gt heps]
        <;> ring
      _ ≤ sourceOneRunQueryCore runtimeConstant dim radius eps / eps ^ 2 :=
        div_le_div_of_nonneg_right hcoldHotShape hepsSq.le
  simpa only [Nat.cast_mul, Nat.cast_ofNat, k] using
    (coldHotPhaseSum_le_sourceBudget_of_real runtimeConstant dim (2 * k)
      cold hot radius eps coldMean hotMean hcold hhot hreal)

/-- Literal finite-prefix readout of the weighted Gaussian phase product. -/
noncomputable def gaussianScorePrefixReadout
    (chainLength m k : Nat) (sigmaSq : Nat → Real) (K : Set (State n))
    (initialNormalizer : Real)
    (z : Fin k → ((Finset.Iic m → State n) × State n)) : Real :=
  initialNormalizer * ∏ j ∈ Finset.range m,
    if hj : j < m then
      ((∑ l : Fin k, phaseScore chainLength sigmaSq (interior K) j
        ((z l).1 ⟨j + 1, Finset.mem_Iic.2 (by omega)⟩)) / (k : Real))
    else 1

theorem measurable_gaussianScorePrefixReadout
    {chainLength m k : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    (initialNormalizer : Real) :
    Measurable (gaussianScorePrefixReadout chainLength m k sigmaSq K
      initialNormalizer) := by
  unfold gaussianScorePrefixReadout
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro j hj
  simp only [dif_pos (Finset.mem_range.mp hj)]
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro l _hl
  exact (measurable_phaseScore (m := chainLength) (σsq := sigmaSq)
    (K := interior K) isOpen_interior.measurableSet j).comp
      ((measurable_pi_apply _).comp
        (measurable_fst.comp (measurable_pi_apply l)))

/-- Reading the stored finite score prefix is definitionally the same estimator as the
ordinary doubled-stream path statistic. -/
theorem gaussianScorePrefixReadout_independentPathScorePrefixCurrent
    {chainLength m k : Nat} {sigmaSq : Nat → Real} {K : Set (State n)}
    (initialNormalizer : Real)
    (omega : Fin k → Nat → State n × State n) :
    gaussianScorePrefixReadout chainLength m k sigmaSq K initialNormalizer
        (independentPathScorePrefixCurrent m omega) =
      initialNormalizer * phaseProduct
        (fun j ↦ streamAverage (k := k)
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            chainLength sigmaSq K j)) m omega := by
  unfold gaussianScorePrefixReadout phaseProduct streamAverage Ttc.CVEst.avgOf
    streamScore independentPathScorePrefixCurrent pathScorePrefixCurrent
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [dif_pos (Finset.mem_range.mp hj)]
  rfl

/-! ## Literal operational cold/hot Gaussian schedules -/

/-- The honest source hybrid implementation: radius-four phase-indexed Gaussian
kernels in the cold block and full-body finite-retry Gaussian kernels in the hot block.
The hot parameters are locally indexed from zero after the cold boundary. -/
noncomputable def operationalGaussianColdHotCostedSchedule
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat) :
    Nat → Kernel (State n) (ENNReal × (State n × State n)) :=
  coldHotCostedSchedule cold
    (coldGaussianCostedKernel hn K hK s0 hs0 coldRetrySteps coldRetries)
    (gaussianFiniteScoreSeedCostedSchedule K hK hotDelta hotSigmaSq hotShrink
      hhotDelta hhotShrink hotRetrySteps hotRetries)

instance operationalGaussianColdHotCostedSchedule.isMarkovKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat) (i : Nat) :
    IsMarkovKernel (operationalGaussianColdHotCostedSchedule hn K hK s0 hs0
      coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink hhotDelta
      hhotShrink hotRetrySteps hotRetries i) := by
  unfold operationalGaussianColdHotCostedSchedule
  infer_instance

/-- Cost erasure of the literal source hybrid schedule. -/
noncomputable def operationalGaussianColdHotSchedule
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat) :
    Nat → Kernel (State n) (State n × State n) :=
  coldHotSchedule cold
    (coldGaussianKernel hn K hK s0 hs0 coldRetrySteps coldRetries)
    (gaussianFiniteScoreSeedSchedule K hK hotDelta hotSigmaSq hotShrink
      hhotDelta hhotShrink hotRetrySteps hotRetries)

instance operationalGaussianColdHotSchedule.isMarkovKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat) (i : Nat) :
    IsMarkovKernel (operationalGaussianColdHotSchedule hn K hK s0 hs0
      coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink hhotDelta
      hhotShrink hotRetrySteps hotRetries i) := by
  unfold operationalGaussianColdHotSchedule
  infer_instance

/-- Exact cost erasure for the honest radius-four/full-body splice. -/
theorem map_snd_operationalGaussianColdHotCostedSchedule
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (operationalGaussianColdHotCostedSchedule hn K hK s0 hs0
          coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink hhotDelta
          hhotShrink hotRetrySteps hotRetries i x) =
      operationalGaussianColdHotSchedule hn K hK s0 hs0 coldRetrySteps
        coldRetries cold hotDelta hotSigmaSq hotShrink hhotDelta hhotShrink
        hotRetrySteps hotRetries i x := by
  apply map_snd_coldHotCostedSchedule
  · exact map_snd_coldGaussianCostedKernel hn K hK s0 hs0
      coldRetrySteps coldRetries
  · exact map_snd_gaussianFiniteScoreSeedCostedSchedule K hK hotDelta hotSigmaSq
      hotShrink hhotDelta hhotShrink hotRetrySteps hotRetries

/-- Phase cost of the honest splice reduces exactly to its cold or hot component. -/
theorem heterogeneousStepMean_operationalGaussianColdHotCostedSchedule
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (i : Nat) (x : State n) :
    heterogeneousStepMean
        (operationalGaussianColdHotCostedSchedule hn K hK s0 hs0
          coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink hhotDelta
          hhotShrink hotRetrySteps hotRetries i) x =
      if i < cold then heterogeneousStepMean
        (coldGaussianCostedKernel hn K hK s0 hs0 coldRetrySteps coldRetries i) x
      else heterogeneousStepMean
        (gaussianFiniteScoreSeedCostedSchedule K hK hotDelta hotSigmaSq hotShrink
          hhotDelta hhotShrink hotRetrySteps hotRetries (i - cold)) x := by
  exact heterogeneousStepMean_coldHotCostedSchedule cold
    (coldGaussianCostedKernel hn K hK s0 hs0 coldRetrySteps coldRetries)
    (gaussianFiniteScoreSeedCostedSchedule K hK hotDelta hotSigmaSq hotShrink
      hhotDelta hhotShrink hotRetrySteps hotRetries) i x

/-- Operationally proved hot variant: the cold block is still the honest radius-four
kernel, while the full-body hot block uses the repository's random-fallback Gaussian
kernel.  This is the form consumed by the existing adaptive operational package. -/
noncomputable def operationalGaussianColdHotFallbackCostedSchedule
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (fallback : Nat → Measure (State n × State n))
    [∀ i, IsProbabilityMeasure (fallback i)] :
    Nat → Kernel (State n) (ENNReal × (State n × State n)) :=
  coldHotCostedSchedule cold
    (coldGaussianCostedKernel hn K hK s0 hs0 coldRetrySteps coldRetries)
    (warmFallbackCostedSchedule K hK hotDelta hotSigmaSq hotShrink
      hhotDelta hhotShrink hotRetrySteps hotRetries fallback)

noncomputable def operationalGaussianColdHotFallbackSchedule
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (fallback : Nat → Measure (State n × State n))
    [∀ i, IsProbabilityMeasure (fallback i)] :
    Nat → Kernel (State n) (State n × State n) :=
  coldHotSchedule cold
    (coldGaussianKernel hn K hK s0 hs0 coldRetrySteps coldRetries)
    (warmFallbackSchedule K hK hotDelta hotSigmaSq hotShrink
      hhotDelta hhotShrink hotRetrySteps hotRetries fallback)

instance operationalGaussianColdHotFallbackCostedSchedule.isMarkovKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (fallback : Nat → Measure (State n × State n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (operationalGaussianColdHotFallbackCostedSchedule hn K hK s0 hs0
      coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink hhotDelta
      hhotShrink hotRetrySteps hotRetries fallback i) := by
  unfold operationalGaussianColdHotFallbackCostedSchedule
  infer_instance

instance operationalGaussianColdHotFallbackSchedule.isMarkovKernel
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (fallback : Nat → Measure (State n × State n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) :
    IsMarkovKernel (operationalGaussianColdHotFallbackSchedule hn K hK s0 hs0
      coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink hhotDelta
      hhotShrink hotRetrySteps hotRetries fallback i) := by
  unfold operationalGaussianColdHotFallbackSchedule
  infer_instance

/-- Exact cost erasure for the radius-four/random-fallback operational splice. -/
theorem map_snd_operationalGaussianColdHotFallbackCostedSchedule
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat) (cold : Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (fallback : Nat → Measure (State n × State n))
    [∀ i, IsProbabilityMeasure (fallback i)] (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (operationalGaussianColdHotFallbackCostedSchedule hn K hK s0 hs0
          coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink hhotDelta
          hhotShrink hotRetrySteps hotRetries fallback i x) =
      operationalGaussianColdHotFallbackSchedule hn K hK s0 hs0 coldRetrySteps
        coldRetries cold hotDelta hotSigmaSq hotShrink hhotDelta hhotShrink
        hotRetrySteps hotRetries fallback i x := by
  apply map_snd_coldHotCostedSchedule
  · exact map_snd_coldGaussianCostedKernel hn K hK s0 hs0
      coldRetrySteps coldRetries
  · intro j y
    exact map_snd_gaussianWarmFallbackCostedPhaseKernel hK (hotDelta j)
      (hotSigmaSq j) (hotShrink j) (hhotDelta j) (hhotShrink j)
      (hotRetrySteps j) (hotRetries j) (fallback j) y

/-- End-to-end per-input source certificate for the concrete finite-retry Gaussian
schedule.  `haccuracy` is a statement on its ordinary uncosted path law (for example
the output of `relative_weighted_accuracy_four_fifths_sourceSharp`); the theorem
transfers it definitionally to retained score histories and closes every cost-erasure
and source-budget obligation. -/
theorem exists_sourceReferenceTVOneRunCertificate_gaussianFinite_coldHot
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu : Measure (State n × State n)) [IsProbabilityMeasure mu]
    (tau : Nat → Measure (State n)) [∀ i, IsProbabilityMeasure (tau i)]
    (e : Nat → ENNReal)
    {runtimeConstant radius eps : Real} {dim cold hot hotChunks : Nat}
    (hn : 1 ≤ dim) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (coldMean hotMean : Nat → Real)
    (hcold : ∀ i, 0 ≤ coldMean i) (hhot : ∀ i, 0 ≤ hotMean i)
    (htau0 : Measure.map Prod.snd mu = tau 0)
    (hphaseSeedTV : ∀ i,
      TVLe ((tau i).bind
        (Kernel.map
          (gaussianFiniteScoreSeedCostedSchedule K hK delta sigmaSq shrink
            hdelta hshrink retrySteps retries i)
          (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
        (tau (i + 1)) (e i))
    (hphaseCost : ∀ i,
      (∫⁻ x, heterogeneousStepMean
        (gaussianFiniteScoreSeedCostedSchedule K hK delta sigmaSq shrink
          hdelta hshrink retrySteps retries i) x ∂tau i) ≤
        coldHotPhaseMean cold hot coldMean hotMean i)
    (hcoldHotShape :
      20000 * weightedSampleNumerator dim cold hotChunks *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i) ≤
        sourceOneRunQueryCore runtimeConstant dim radius eps)
    (readout :
      (Fin (2 * estimatorSamples dim cold hotChunks (eps / 100)) →
        ((Finset.Iic (cold + hot) → State n) × State n)) → Real)
    (hreadout : Measurable readout) {lo hi : Real}
    (herror :
      (2 * estimatorSamples dim cold hotChunks (eps / 100) : ENNReal) *
          (∑ i ∈ Finset.range (cold + hot), e i) ≤
        ENNReal.ofReal (1 / 40 : Real))
    (haccuracy : 4 / 5 ≤
      (Ttc.CVIndependentStreamDependence.independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (Ttc.CVScoreSeedPhaseKernel.stateScheduleFromSeed
          (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink
            hdelta hshrink retrySteps retries)) mu).real
        {omega | readout
          (independentPathScorePrefixCurrent (cold + hot) omega) ∈ Icc lo hi}) :
    ∃ reference : Measure
        (Fin (2 * estimatorSamples dim cold hotChunks (eps / 100)) →
          HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (independentHeterogeneousRetainedPathLaw
          (2 * estimatorSamples dim cold hotChunks (eps / 100))
          (gaussianFiniteScoreSeedCostedSchedule K hK delta sigmaSq shrink
            hdelta hshrink retrySteps retries) mu (cold + hot))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ readout
          (independentStoredScorePrefixCurrent (cold + hot) omega))
        runtimeConstant dim radius eps lo hi := by
  let k := estimatorSamples dim cold hotChunks (eps / 100)
  have hbudget := doubledEstimator_innerHundred_coldHotPhaseSum_le_sourceBudget
    (runtimeConstant := runtimeConstant) (radius := radius) (dim := dim)
    (cold := cold) (hot := hot) (hotChunks := hotChunks)
    hn heps heps1 coldMean hotMean hcold hhot hcoldHotShape
  have hinitState : Measure.map Prod.snd
      (initialHeterogeneousHistoryLaw mu) = tau 0 := by
    rw [map_snd_initialHeterogeneousHistoryLaw, htau0]
  have hbudget' : ((2 * k : Nat) : ENNReal) *
      (0 + ∑ i ∈ Finset.range (cold + hot),
        coldHotPhaseMean cold hot coldMean hotMean i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant dim radius eps := by
    simpa only [zero_add, Nat.cast_mul, Nat.cast_ofNat, k] using hbudget
  have herror' : ((2 * k : Nat) : ENNReal) *
      (0 + ∑ i ∈ Finset.range (cold + hot), e i) ≤
        ENNReal.ofReal (1 / 40 : Real) := by
    simpa only [zero_add, Nat.cast_mul, Nat.cast_ofNat, k] using herror
  simpa only [k] using
    (exists_sourceReferenceTVOneRunCertificate_of_pathReadoutAccuracy
      (gaussianFiniteScoreSeedCostedSchedule K hK delta sigmaSq shrink
        hdelta hshrink retrySteps retries)
      (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink
        hdelta hshrink retrySteps retries)
      mu
      (fun i x ↦ map_snd_gaussianFiniteScoreSeedCostedSchedule K hK delta sigmaSq
        shrink hdelta hshrink retrySteps retries i x)
      (initialHeterogeneousHistoryLaw mu) tau e
      (coldHotPhaseMean cold hot coldMean hotMean)
      (d := 0) (initialBudget := 0) (TVLe.refl _) hinitState
      (by simpa using lintegral_initialHeterogeneousHistoryCost mu)
      hphaseSeedTV hphaseCost dim (cold + hot) (2 * k) readout hreadout
      herror' hbudget' haccuracy)

/-- Same concrete certificate with the ordinary weighted phase product as its only
accuracy premise.  The finite retained-history readout is constructed internally. -/
theorem exists_sourceReferenceTVOneRunCertificate_gaussianFinite_weightedProduct
    {K : Set (State n)} (hK : MeasurableSet K)
    (delta sigmaSq shrink : Nat → Real)
    (hdelta : ∀ i, 0 < delta i) (hshrink : ∀ i, shrink i ≠ 0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    (mu : Measure (State n × State n)) [IsProbabilityMeasure mu]
    (tau : Nat → Measure (State n)) [∀ i, IsProbabilityMeasure (tau i)]
    (e : Nat → ENNReal)
    {runtimeConstant radius eps : Real} {dim cold hot hotChunks chainLength : Nat}
    (hn : 1 ≤ dim) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (coldMean hotMean : Nat → Real)
    (hcold : ∀ i, 0 ≤ coldMean i) (hhot : ∀ i, 0 ≤ hotMean i)
    (htau0 : Measure.map Prod.snd mu = tau 0)
    (hphaseSeedTV : ∀ i,
      TVLe ((tau i).bind
        (Kernel.map
          (gaussianFiniteScoreSeedCostedSchedule K hK delta sigmaSq shrink
            hdelta hshrink retrySteps retries i)
          (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
        (tau (i + 1)) (e i))
    (hphaseCost : ∀ i,
      (∫⁻ x, heterogeneousStepMean
        (gaussianFiniteScoreSeedCostedSchedule K hK delta sigmaSq shrink
          hdelta hshrink retrySteps retries i) x ∂tau i) ≤
        coldHotPhaseMean cold hot coldMean hotMean i)
    (hcoldHotShape :
      20000 * weightedSampleNumerator dim cold hotChunks *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i) ≤
        sourceOneRunQueryCore runtimeConstant dim radius eps)
    (initialNormalizer : Real) {lo hi : Real}
    (herror :
      (2 * estimatorSamples dim cold hotChunks (eps / 100) : ENNReal) *
          (∑ i ∈ Finset.range (cold + hot), e i) ≤
        ENNReal.ofReal (1 / 40 : Real))
    (haccuracy : 4 / 5 ≤
      (Ttc.CVIndependentStreamDependence.independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (Ttc.CVScoreSeedPhaseKernel.stateScheduleFromSeed
          (gaussianFiniteScoreSeedSchedule K hK delta sigmaSq shrink
            hdelta hshrink retrySteps retries)) mu).real
        {omega | initialNormalizer * phaseProduct
          (fun j ↦ streamAverage
            (k := 2 * estimatorSamples dim cold hotChunks (eps / 100))
            (positiveScalarPhaseFamilyChainLength (Seed := State n)
              chainLength sigmaSq K j)) (cold + hot) omega ∈ Icc lo hi}) :
    ∃ reference : Measure
        (Fin (2 * estimatorSamples dim cold hotChunks (eps / 100)) →
          HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (independentHeterogeneousRetainedPathLaw
          (2 * estimatorSamples dim cold hotChunks (eps / 100))
          (gaussianFiniteScoreSeedCostedSchedule K hK delta sigmaSq shrink
            hdelta hshrink retrySteps retries) mu (cold + hot))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ gaussianScorePrefixReadout chainLength (cold + hot)
          (2 * estimatorSamples dim cold hotChunks (eps / 100)) sigmaSq K
          initialNormalizer (independentStoredScorePrefixCurrent (cold + hot) omega))
        runtimeConstant dim radius eps lo hi := by
  apply exists_sourceReferenceTVOneRunCertificate_gaussianFinite_coldHot
    hK delta sigmaSq shrink hdelta hshrink retrySteps retries mu tau e
    hn heps heps1 coldMean hotMean hcold hhot htau0 hphaseSeedTV hphaseCost
    hcoldHotShape
    (gaussianScorePrefixReadout chainLength (cold + hot)
      (2 * estimatorSamples dim cold hotChunks (eps / 100)) sigmaSq K
      initialNormalizer)
    (measurable_gaussianScorePrefixReadout initialNormalizer)
    herror
  simpa only [gaussianScorePrefixReadout_independentPathScorePrefixCurrent] using
    haccuracy

/-- Honest heterogeneous cold/hot assembly.  The cold and hot implementations may use
different bodies, step sizes, and retry policies.  Only their exact cost-erasure laws
are needed here; the retained-history reference, doubled-stream source budget, and
finite weighted-product readout are then constructed internally. -/
theorem exists_sourceReferenceTVOneRunCertificate_operationalColdHot_weightedProduct
    (Qcold Qhot : Nat →
      Kernel (State n) (ENNReal × (State n × State n)))
    (Pcold Phot : Nat → Kernel (State n) (State n × State n))
    [∀ i, IsMarkovKernel (Qcold i)] [∀ i, IsMarkovKernel (Qhot i)]
    [∀ i, IsMarkovKernel (Pcold i)] [∀ i, IsMarkovKernel (Phot i)]
    (mu : Measure (State n × State n)) [IsProbabilityMeasure mu]
    (tau : Nat → Measure (State n)) [∀ i, IsProbabilityMeasure (tau i)]
    (e : Nat → ENNReal)
    {runtimeConstant radius eps : Real}
    {dim cold hot hotChunks chainLength : Nat}
    (hn : 1 ≤ dim) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (sigmaSq : Nat → Real) (K : Set (State n))
    (hcoldForget : ∀ i x, Measure.map Prod.snd (Qcold i x) = Pcold i x)
    (hhotForget : ∀ i x, Measure.map Prod.snd (Qhot i x) = Phot i x)
    (coldMean hotMean : Nat → Real)
    (hcold : ∀ i, 0 ≤ coldMean i) (hhot : ∀ i, 0 ≤ hotMean i)
    (htau0 : Measure.map Prod.snd mu = tau 0)
    (hphaseSeedTV : ∀ i, i < cold + hot →
      TVLe ((tau i).bind
        (Kernel.map (coldHotCostedSchedule cold Qcold Qhot i)
          (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
        (tau (i + 1)) (e i))
    (hphaseCost : ∀ i, i < cold + hot →
      (∫⁻ x, heterogeneousStepMean
        (coldHotCostedSchedule cold Qcold Qhot i) x ∂tau i) ≤
        coldHotPhaseMean cold hot coldMean hotMean i)
    (hcoldHotShape :
      20000 * weightedSampleNumerator dim cold hotChunks *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i) ≤
        sourceOneRunQueryCore runtimeConstant dim radius eps)
    (initialNormalizer : Real) {lo hi : Real}
    (herror :
      (2 * estimatorSamples dim cold hotChunks (eps / 100) : ENNReal) *
          (∑ i ∈ Finset.range (cold + hot), e i) ≤
        ENNReal.ofReal (1 / 40 : Real))
    (haccuracy : 4 / 5 ≤
      (Ttc.CVIndependentStreamDependence.independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (Ttc.CVScoreSeedPhaseKernel.stateScheduleFromSeed
          (coldHotSchedule cold Pcold Phot)) mu).real
        {omega | initialNormalizer * phaseProduct
          (fun j ↦ streamAverage
            (k := 2 * estimatorSamples dim cold hotChunks (eps / 100))
            (positiveScalarPhaseFamilyChainLength (Seed := State n)
              chainLength sigmaSq K j)) (cold + hot) omega ∈ Icc lo hi}) :
    ∃ reference : Measure
        (Fin (2 * estimatorSamples dim cold hotChunks (eps / 100)) →
          HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (independentHeterogeneousRetainedPathLaw
          (2 * estimatorSamples dim cold hotChunks (eps / 100))
          (coldHotCostedSchedule cold Qcold Qhot) mu (cold + hot))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ gaussianScorePrefixReadout chainLength (cold + hot)
          (2 * estimatorSamples dim cold hotChunks (eps / 100)) sigmaSq K
          initialNormalizer (independentStoredScorePrefixCurrent (cold + hot) omega))
        runtimeConstant dim radius eps lo hi := by
  let k := estimatorSamples dim cold hotChunks (eps / 100)
  let phaseBound : Nat → ENNReal := fun i ↦
    if i < cold + hot then coldHotPhaseMean cold hot coldMean hotMean i
    else ∫⁻ x, heterogeneousStepMean
      (coldHotCostedSchedule cold Qcold Qhot i) x ∂tau i
  let phaseError : Nat → ENNReal := fun i ↦
    if i < cold + hot then e i else ⊤
  have hbudget := doubledEstimator_innerHundred_coldHotPhaseSum_le_sourceBudget
    (runtimeConstant := runtimeConstant) (radius := radius) (dim := dim)
    (cold := cold) (hot := hot) (hotChunks := hotChunks)
    hn heps heps1 coldMean hotMean hcold hhot hcoldHotShape
  have hinitState : Measure.map Prod.snd
      (initialHeterogeneousHistoryLaw mu) = tau 0 := by
    rw [map_snd_initialHeterogeneousHistoryLaw, htau0]
  have hsumBound :
      (∑ i ∈ Finset.range (cold + hot), phaseBound i) =
        ∑ i ∈ Finset.range (cold + hot),
          coldHotPhaseMean cold hot coldMean hotMean i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [phaseBound, if_pos (Finset.mem_range.mp hi)]
  have hbudget' : ((2 * k : Nat) : ENNReal) *
      (0 + ∑ i ∈ Finset.range (cold + hot),
        phaseBound i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant dim radius eps := by
    rw [hsumBound]
    simpa only [zero_add, Nat.cast_mul, Nat.cast_ofNat, k] using hbudget
  have hsumError :
      (∑ i ∈ Finset.range (cold + hot), phaseError i) =
        ∑ i ∈ Finset.range (cold + hot), e i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [phaseError, if_pos (Finset.mem_range.mp hi)]
  have herror' : ((2 * k : Nat) : ENNReal) *
      (0 + ∑ i ∈ Finset.range (cold + hot), phaseError i) ≤
        ENNReal.ofReal (1 / 40 : Real) := by
    rw [hsumError]
    simpa only [zero_add, Nat.cast_mul, Nat.cast_ofNat, k] using herror
  have hforget : ∀ i x,
      Measure.map Prod.snd (coldHotCostedSchedule cold Qcold Qhot i x) =
        coldHotSchedule cold Pcold Phot i x :=
    map_snd_coldHotCostedSchedule cold Qcold Qhot Pcold Phot
      hcoldForget hhotForget
  have hphaseCost' : ∀ i,
      (∫⁻ x, heterogeneousStepMean
        (coldHotCostedSchedule cold Qcold Qhot i) x ∂tau i) ≤ phaseBound i := by
    intro i
    by_cases hi : i < cold + hot
    · simpa only [phaseBound, if_pos hi] using hphaseCost i hi
    · simp only [phaseBound, if_neg hi]
      exact le_rfl
  have hphaseSeedTV' : ∀ i,
      TVLe ((tau i).bind
        (Kernel.map (coldHotCostedSchedule cold Qcold Qhot i)
          (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
        (tau (i + 1)) (phaseError i) := by
    intro i
    by_cases hi : i < cold + hot
    · simpa only [phaseError, if_pos hi] using hphaseSeedTV i hi
    · simpa only [phaseError, if_neg hi] using
        (Arlib.tvLe_top
          ((tau i).bind
            (Kernel.map (coldHotCostedSchedule cold Qcold Qhot i)
              (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
          (tau (i + 1)))
  apply exists_sourceReferenceTVOneRunCertificate_of_pathReadoutAccuracy
    (coldHotCostedSchedule cold Qcold Qhot)
    (coldHotSchedule cold Pcold Phot) mu hforget
    (initialHeterogeneousHistoryLaw mu) tau phaseError
    phaseBound
    (d := 0) (initialBudget := 0) (TVLe.refl _) hinitState
    (by simpa using lintegral_initialHeterogeneousHistoryCost mu)
    hphaseSeedTV' hphaseCost' dim (cold + hot) (2 * k)
    (gaussianScorePrefixReadout chainLength (cold + hot) (2 * k) sigmaSq K
      initialNormalizer)
    (measurable_gaussianScorePrefixReadout initialNormalizer)
    herror' hbudget'
  simpa only [k, gaussianScorePrefixReadout_independentPathScorePrefixCurrent] using
    haccuracy

/-- Concrete per-input certificate for the literal radius-four/full-body Gaussian
splice.  Cost erasure for both sides of the boundary is completely internal. -/
theorem exists_sourceReferenceTVOneRunCertificate_operationalGaussianColdHot
    (hn : 1 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (s0 : Real) (hs0 : 0 < s0)
    (coldRetrySteps : Nat → Nat → Nat) (coldRetries : Nat → Nat)
    (hotDelta hotSigmaSq hotShrink : Nat → Real)
    (hhotDelta : ∀ i, 0 < hotDelta i)
    (hhotShrink : ∀ i, hotShrink i ≠ 0)
    (hotRetrySteps : Nat → Nat → Nat) (hotRetries : Nat → Nat)
    (scoreSigmaSq : Nat → Real)
    (mu : Measure (State n × State n)) [IsProbabilityMeasure mu]
    (tau : Nat → Measure (State n)) [∀ i, IsProbabilityMeasure (tau i)]
    (e : Nat → ENNReal)
    {runtimeConstant radius eps : Real} {cold hot hotChunks chainLength : Nat}
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (coldMean hotMean : Nat → Real)
    (hcold : ∀ i, 0 ≤ coldMean i) (hhot : ∀ i, 0 ≤ hotMean i)
    (htau0 : Measure.map Prod.snd mu = tau 0)
    (hphaseSeedTV : ∀ i, i < cold + hot →
      TVLe ((tau i).bind
        (Kernel.map
          (operationalGaussianColdHotCostedSchedule hn K hK s0 hs0
            coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink
            hhotDelta hhotShrink hotRetrySteps hotRetries i)
          (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
        (tau (i + 1)) (e i))
    (hphaseCost : ∀ i, i < cold + hot →
      (∫⁻ x, heterogeneousStepMean
        (operationalGaussianColdHotCostedSchedule hn K hK s0 hs0
          coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink
          hhotDelta hhotShrink hotRetrySteps hotRetries i) x ∂tau i) ≤
        coldHotPhaseMean cold hot coldMean hotMean i)
    (hcoldHotShape :
      20000 * weightedSampleNumerator n cold hotChunks *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i) ≤
        sourceOneRunQueryCore runtimeConstant n radius eps)
    (initialNormalizer : Real) {lo hi : Real}
    (herror :
      (2 * estimatorSamples n cold hotChunks (eps / 100) : ENNReal) *
          (∑ i ∈ Finset.range (cold + hot), e i) ≤
        ENNReal.ofReal (1 / 40 : Real))
    (haccuracy : 4 / 5 ≤
      (independentPathLaw
        (2 * estimatorSamples n cold hotChunks (eps / 100))
        (stateScheduleFromSeed
          (operationalGaussianColdHotSchedule hn K hK s0 hs0
            coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink
            hhotDelta hhotShrink hotRetrySteps hotRetries)) mu).real
        {omega | initialNormalizer * phaseProduct
          (fun j ↦ streamAverage
            (k := 2 * estimatorSamples n cold hotChunks (eps / 100))
            (positiveScalarPhaseFamilyChainLength (Seed := State n)
              chainLength scoreSigmaSq K j)) (cold + hot) omega ∈ Icc lo hi}) :
    ∃ reference : Measure
        (Fin (2 * estimatorSamples n cold hotChunks (eps / 100)) →
          HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (independentHeterogeneousRetainedPathLaw
          (2 * estimatorSamples n cold hotChunks (eps / 100))
          (operationalGaussianColdHotCostedSchedule hn K hK s0 hs0
            coldRetrySteps coldRetries cold hotDelta hotSigmaSq hotShrink
            hhotDelta hhotShrink hotRetrySteps hotRetries)
          mu (cold + hot))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ gaussianScorePrefixReadout chainLength (cold + hot)
          (2 * estimatorSamples n cold hotChunks (eps / 100)) scoreSigmaSq K
          initialNormalizer (independentStoredScorePrefixCurrent (cold + hot) omega))
        runtimeConstant n radius eps lo hi := by
  apply exists_sourceReferenceTVOneRunCertificate_operationalColdHot_weightedProduct
    (coldGaussianCostedKernel hn K hK s0 hs0 coldRetrySteps coldRetries)
    (gaussianFiniteScoreSeedCostedSchedule K hK hotDelta hotSigmaSq hotShrink
      hhotDelta hhotShrink hotRetrySteps hotRetries)
    (coldGaussianKernel hn K hK s0 hs0 coldRetrySteps coldRetries)
    (gaussianFiniteScoreSeedSchedule K hK hotDelta hotSigmaSq hotShrink
      hhotDelta hhotShrink hotRetrySteps hotRetries)
    mu tau e hn heps heps1 scoreSigmaSq K
    (map_snd_coldGaussianCostedKernel hn K hK s0 hs0
      coldRetrySteps coldRetries)
    (map_snd_gaussianFiniteScoreSeedCostedSchedule K hK hotDelta hotSigmaSq
      hotShrink hhotDelta hhotShrink hotRetrySteps hotRetries)
    coldMean hotMean hcold hhot htau0 hphaseSeedTV hphaseCost hcoldHotShape
    initialNormalizer herror haccuracy

/-- The preceding honest cold/hot certificate with its accuracy premise generated by
the repaired source-sharp weighted theorem.  Taking the implemented phase statistic to
be the literal Gaussian stream average makes the exact-readout event `univ`, so no
additional estimator approximation is hidden in this assembly. -/
theorem exists_sourceReferenceTVOneRunCertificate_operationalColdHot_sourceSharp
    (Qcold Qhot : Nat →
      Kernel (State n) (ENNReal × (State n × State n)))
    (Pcold Phot : Nat → Kernel (State n) (State n × State n))
    [∀ i, IsMarkovKernel (Qcold i)] [∀ i, IsMarkovKernel (Qhot i)]
    [∀ i, IsMarkovKernel (Pcold i)] [∀ i, IsMarkovKernel (Phot i)]
    (mu : Measure (State n × State n)) [IsProbabilityMeasure mu]
    (tauSeed : Nat → Measure (State n)) [∀ i, IsProbabilityMeasure (tauSeed i)]
    (e : Nat → ENNReal)
    {runtimeConstant radius eps eta beta requested R : Real}
    {dim cold hot hotChunks chainLength : Nat}
    (hn : 1 ≤ dim) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hbeta : 0 ≤ beta)
    (haccuracyBudget : eta + beta + eta * beta ≤ requested)
    (sigmaSq : Nat → Real) (K : Set (State n)) (C factor : Nat → Real)
    (V : Nat →
      (Fin (2 * estimatorSamples dim cold hotChunks (eps / 100)) →
        Nat → State n × State n) → Real)
    (hop : IndependentStreamOperational
      (2 * estimatorSamples dim cold hotChunks (eps / 100))
      (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot))
      (coldHotSchedule cold Pcold Phot) Prod.snd mu V (cold + hot) eta)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (cold + hot)
      (scoreAwareMixError (cold + hot)
        (2 * estimatorSamples dim cold hotChunks (eps / 100)) eta
        (relativePhaseSlack chainLength sigmaSq K C)
        (relativePhaseBoundSq R sigmaSq C)) j)
    (hcoldForget : ∀ i x, Measure.map Prod.snd (Qcold i x) = Pcold i x)
    (hhotForget : ∀ i x, Measure.map Prod.snd (Qhot i x) = Phot i x)
    (coldMean hotMean : Nat → Real)
    (hcold : ∀ i, 0 ≤ coldMean i) (hhot : ∀ i, 0 ≤ hotMean i)
    (htau0 : Measure.map Prod.snd mu = tauSeed 0)
    (hphaseSeedTV : ∀ i, i < cold + hot →
      TVLe ((tauSeed i).bind
        (Kernel.map (coldHotCostedSchedule cold Qcold Qhot i)
          (fun y : ENNReal × (State n × State n) ↦ y.2.2)))
        (tauSeed (i + 1)) (e i))
    (hphaseCost : ∀ i, i < cold + hot →
      (∫⁻ x, heterogeneousStepMean
        (coldHotCostedSchedule cold Qcold Qhot i) x ∂tauSeed i) ≤
        coldHotPhaseMean cold hot coldMean hotMean i)
    (hcoldHotShape :
      20000 * weightedSampleNumerator dim cold hotChunks *
          ((∑ i ∈ Finset.range cold, coldMean i) +
            ∑ i ∈ Finset.range hot, hotMean i) ≤
        sourceOneRunQueryCore runtimeConstant dim radius eps)
    (herror :
      (2 * estimatorSamples dim cold hotChunks (eps / 100) : ENNReal) *
          (∑ i ∈ Finset.range (cold + hot), e i) ≤
        ENNReal.ofReal (1 / 40 : Real))
    (hm : 0 < cold + hot)
    (hsigma : ∀ j, 0 < sigmaSq j) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (hKR : K ⊆ closedBall (0 : State n) R)
    (htarget : ∀ i, Measure.map Prod.fst (hop.tau i) =
      coolLaw chainLength sigmaSq K i)
    (hC1 : ∀ i, 1 < C i)
    (hWint : ∀ j, Integrable
      (fun omega => streamAverage
        (k := 2 * estimatorSamples dim cold hotChunks (eps / 100))
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          chainLength sigmaSq K j) omega)
      (independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu))
    (hW2int : ∀ j, Integrable
      (fun omega => (streamAverage
        (k := 2 * estimatorSamples dim cold hotChunks (eps / 100))
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          chainLength sigmaSq K j) omega) ^ 2)
      (independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu))
    (hWEpos : ∀ j, 0 < ∫ omega, streamAverage
      (k := 2 * estimatorSamples dim cold hotChunks (eps / 100))
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        chainLength sigmaSq K j) omega
      ∂(independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu))
    (hrawSecond : ∀ j, ∫ omega, (streamAverage
      (k := 2 * estimatorSamples dim cold hotChunks (eps / 100))
      (positiveScalarPhaseFamilyChainLength (Seed := State n)
        chainLength sigmaSq K j) omega) ^ 2
      ∂(independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu) ≤
      2 * (∫ omega, streamAverage
        (k := 2 * estimatorSamples dim cold hotChunks (eps / 100))
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          chainLength sigmaSq K j) omega
        ∂(independentPathLaw
          (2 * estimatorSamples dim cold hotChunks (eps / 100))
          (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu)) ^ 2)
    (hVdef : ∀ j omega, V j omega = min
      (streamAverage
        (k := 2 * estimatorSamples dim cold hotChunks (eps / 100))
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          chainLength sigmaSq K j) omega)
      (correctedAlpha (cold + hot) eta * ∫ z, streamAverage
        (k := 2 * estimatorSamples dim cold hotChunks (eps / 100))
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          chainLength sigmaSq K j) z
        ∂(independentPathLaw
          (2 * estimatorSamples dim cold hotChunks (eps / 100))
          (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu)))
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hEpos : ∀ j, 0 < ∫ omega, V j omega
      ∂(independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu))
    (hVcap : ∀ j omega, V j omega ≤ 2 * correctedAlpha (cold + hot) eta *
      ∫ z, V j z ∂(independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu))
    (hV2 : ∀ j, Integrable (fun omega => (V j omega) ^ 2)
      (independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu))
    (hV2cap : ∀ j omega, (V j omega) ^ 2 ≤
      2 * correctedAlpha (cold + hot) eta ^ 2 *
        ∫ z, (V j z) ^ 2 ∂(independentPathLaw
          (2 * estimatorSamples dim cold hotChunks (eps / 100))
          (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu))
    (hfactor0 : ∀ j, 0 ≤ factor j)
    (hphaseMoment : ∀ j, ∫ omega, (V j omega) ^ 2
      ∂(independentPathLaw
        (2 * estimatorSamples dim cold hotChunks (eps / 100))
        (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu) ≤
      factor j * (∫ omega, V j omega
        ∂(independentPathLaw
          (2 * estimatorSamples dim cold hotChunks (eps / 100))
          (stateScheduleFromSeed (coldHotSchedule cold Pcold Phot)) mu)) ^ 2)
    (hprefix : ∀ i, i ≤ cold + hot →
      prefixMomentRatio factor i ≤ 1 + eta ^ 2 / 6250)
    (initialNormalizer volumeTarget : Real)
    (hinit : 0 ≤ initialNormalizer) (hvolume : 0 ≤ volumeTarget)
    (hinitChain : initialNormalizer = chain chainLength sigmaSq K 0)
    (htargetChain : volumeTarget = chain chainLength sigmaSq K (cold + hot))
    (hbetaDef : ((cold + hot : Nat) : Real) /
        (2 * correctedAlpha (cold + hot) eta) +
      scoreAwareMeanGamma (cold + hot)
        (2 * estimatorSamples dim cold hotChunks (eps / 100)) eta +
      (((cold + hot : Nat) : Real) / (2 * correctedAlpha (cold + hot) eta)) *
        scoreAwareMeanGamma (cold + hot)
          (2 * estimatorSamples dim cold hotChunks (eps / 100)) eta ≤ beta) :
    ∃ reference : Measure
        (Fin (2 * estimatorSamples dim cold hotChunks (eps / 100)) →
          HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (independentHeterogeneousRetainedPathLaw
          (2 * estimatorSamples dim cold hotChunks (eps / 100))
          (coldHotCostedSchedule cold Qcold Qhot) mu (cold + hot))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ gaussianScorePrefixReadout chainLength (cold + hot)
          (2 * estimatorSamples dim cold hotChunks (eps / 100)) sigmaSq K
          initialNormalizer (independentStoredScorePrefixCurrent (cold + hot) omega))
        runtimeConstant dim radius eps
          ((1 - requested) * volumeTarget) ((1 + requested) * volumeTarget) := by
  let k := 2 * estimatorSamples dim cold hotChunks (eps / 100)
  let Q := coldHotSchedule cold Pcold Phot
  apply exists_sourceReferenceTVOneRunCertificate_operationalColdHot_weightedProduct
    Qcold Qhot Pcold Phot mu tauSeed e hn heps heps1 sigmaSq K
    hcoldForget hhotForget coldMean hotMean hcold hhot htau0 hphaseSeedTV
    hphaseCost hcoldHotShape initialNormalizer herror
  simpa only [Ttc.relErr, k, Q] using
    (relative_weighted_accuracy_four_fifths_sourceSharp
      (k := k) (m := cold + hot) (chainLength := chainLength)
      (Q := Q) (mu0 := mu) (eps := eta) (beta := beta)
      (requested := requested) (R := R) (sigmaSq := sigmaSq) (K := K)
      (C := C) (factor := factor)
      V (fun j omega ↦ streamAverage (k := k)
        (positiveScalarPhaseFamilyChainLength (Seed := State n)
          chainLength sigmaSq K j) omega)
      hop hmixError heta heta1 hm
      (by
        dsimp only [k]
        exact Nat.mul_pos (by norm_num) (estimatorSamples_pos _ _ _ _))
      hbeta haccuracyBudget hsigma hK hKc hball hfin hKR htarget hC1
      hWint hW2int hWEpos hrawSecond hVdef hVm hV0 hEpos hVcap hV2 hV2cap
      hfactor0 hphaseMoment hprefix
      (by
        intro j
        exact measurable_streamAverage
          (measurable_positiveScalarPhaseFamilyChainLength hK j))
      (Eexact := Set.univ) MeasurableSet.univ (by simp)
      (by intro omega _; rfl)
      initialNormalizer volumeTarget hinit hvolume hinitChain htargetChain hbetaDef)

/-! ## Public radial-log capstone -/

/-- A single audit object for the genuinely input-dependent analytic work left after
the concrete cold/hot assembly.  Its `oneRun` field is produced by
`exists_sourceReferenceTVOneRunCertificate_operationalColdHot_sourceSharp` (or its
literal Gaussian specialization) once truncated-cold cross-warmth, selective TV, and
the Gaussian moment package have been supplied.  Everything after that field is
mechanical public-oracle arithmetic. -/
structure OperationalColdHotRadialAudit
    (n : Nat) (runtimeConstant : Real)
    (radialR radialN : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (actual : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real) where
  reference : ∀ a, Measure (Omega a)
  oneRun : ∀ a,
    SourceReferenceTVOneRunCertificate
      (actual a) (reference a) (cost a) (value a)
      (radialLogEffectiveRuntime runtimeConstant (radialN a.1))
      n (radialR a.1) a.2.1
      ((1 - a.2.1) * (volume a.1).toReal)
      ((1 + a.2.1) * (volume a.1).toReal)

/-- Choose the retained reference laws produced input-by-input by the concrete
cold/hot theorem.  This is the smallest per-dimension constructor: callers provide
only the existential one-run certificates, not a preassembled reference family. -/
noncomputable def operationalColdHotRadialAuditOfOneRunCertificates
    (n : Nat) (runtimeConstant : Real)
    (radialR radialN : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (actual : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : ∀ a, ∃ reference : Measure (Omega a),
      SourceReferenceTVOneRunCertificate
        (actual a) reference (cost a) (value a)
        (radialLogEffectiveRuntime runtimeConstant (radialN a.1))
        n (radialR a.1) a.2.1
        ((1 - a.2.1) * (volume a.1).toReal)
        ((1 + a.2.1) * (volume a.1).toReal)) :
    OperationalColdHotRadialAudit n runtimeConstant radialR radialN
      Omega actual cost value where
  reference a := Classical.choose (hcert a)
  oneRun a := Classical.choose_spec (hcert a)

/-- The single residual audit object gives the complete public radial-log reference-TV
certificate family. -/
theorem radialLogSourcePublicReferenceTVCertificates_of_operationalColdHotAudit
    (n : Nat) (runtimeConstant : Real)
    (radialR radialN : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (actual : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (audit : OperationalColdHotRadialAudit n runtimeConstant radialR radialN
      Omega actual cost value) :
    RadialLogSourcePublicReferenceTVCertificates n runtimeConstant radialR radialN
      Omega actual audit.reference cost value where
  actual_probability a := (audit.oneRun a).actual_probability
  reference_probability a := (audit.oneRun a).reference_probability
  cost_measurable a := (audit.oneRun a).cost_measurable
  value_measurable a := (audit.oneRun a).value_measurable
  path_tv a := (audit.oneRun a).path_tv
  reference_expected_queries a := by
    rw [← sourceOneRunQueryBudget_effective_eq_radialLog]
    exact (audit.oneRun a).reference_expected_queries
  accuracy K eps p _heps _hp _hp1 _hKc _hball _hfin :=
    (audit.oneRun (K, eps, p)).accuracy

/-- Strongest closed public capstone currently supported by the concrete retained-history
route.  A dimension-indexed family of the single audit object becomes an honest
`CVRadialLogExpectedImplementation`; all low-level confidence amplification and stopped
actual-law cost accounting are discharged by the already checked public constructor. -/
noncomputable def cvRadialLogExpectedImplementation_of_operationalColdHotAudits
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR radialN : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ n a, MeasurableSpace (Omega n a)]
    (actual : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (audit : ∀ n, OperationalColdHotRadialAudit n runtimeConstant
      (radialR n) (radialN n) (Omega n) (actual n) (cost n) (value n))
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2,
      Ttc.CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2)
    (hNpos : ∀ n (K : Set (Ttc.Space n)), 0 < radialN n K)
    (hNle : ∀ n (K : Set (Ttc.Space n)) R2,
      Ttc.CVAdmissible K R2 → radialN n K ≤ max 1 R2) :
    CVRadialLogExpectedImplementation :=
  cvRadialLogExpectedImplementationOfReferenceTVFamily runtimeConstant hconstant
    radialR radialN Omega actual (fun n ↦ (audit n).reference) cost value
    (fun n ↦ radialLogSourcePublicReferenceTVCertificates_of_operationalColdHotAudit
      n runtimeConstant (radialR n) (radialN n) (Omega n) (actual n)
      (cost n) (value n) (audit n))
    hrad hNpos hNle

/-- Direct public expected-query implementation from the existential per-input output
of the concrete cold/hot source-sharp theorem. -/
noncomputable def cvRadialLogExpectedImplementation_of_operationalColdHotOneRunCertificates
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR radialN : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ n a, MeasurableSpace (Omega n a)]
    (actual : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n a, ∃ reference : Measure (Omega n a),
      SourceReferenceTVOneRunCertificate
        (actual n a) reference (cost n a) (value n a)
        (radialLogEffectiveRuntime runtimeConstant (radialN n a.1))
        n (radialR n a.1) a.2.1
        ((1 - a.2.1) * (volume a.1).toReal)
        ((1 + a.2.1) * (volume a.1).toReal))
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2,
      Ttc.CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2)
    (hNpos : ∀ n (K : Set (Ttc.Space n)), 0 < radialN n K)
    (hNle : ∀ n (K : Set (Ttc.Space n)) R2,
      Ttc.CVAdmissible K R2 → radialN n K ≤ max 1 R2) :
    CVRadialLogExpectedImplementation :=
  cvRadialLogExpectedImplementation_of_operationalColdHotAudits
    runtimeConstant hconstant radialR radialN Omega actual cost value
    (fun n ↦ operationalColdHotRadialAuditOfOneRunCertificates n runtimeConstant
      (radialR n) (radialN n) (Omega n) (actual n) (cost n) (value n)
      (hcert n))
    hrad hNpos hNle

#print axioms map_snd_initialHeterogeneousHistoryLaw
#print axioms lintegral_initialHeterogeneousHistoryCost
#print axioms coldAcceptedSeedTarget_eq_scaledTruncatedCoolLaw
#print axioms one_le_coldCrossWarmFactor
#print axioms coldCrossWarmFactor_ne_top
#print axioms one_le_coldReferenceWarmBudget
#print axioms coldReferenceWarmBudget_ne_top
#print axioms tvLe_seed_bind_coldGaussianCostedKernel_coldAcceptedSeedTarget
#print axioms isWarm_coldAcceptedSeedTarget_succ
#print axioms isWarm_coldAcceptedSeedTarget_full_succ
#print axioms isWarm_coldRetainedReferenceFamily
#print axioms coldGaussian_referenceCost_le_of_geometry_warm
#print axioms operationalColdRetainedPhaseTVAndCost
#print axioms operationalColdHotRetainedPhaseTVAndCost
#print axioms doubledEstimator_innerHundred_coldHotPhaseSum_le_sourceBudget
#print axioms exists_sourceReferenceTVOneRunCertificate_gaussianFinite_coldHot
#print axioms exists_sourceReferenceTVOneRunCertificate_gaussianFinite_weightedProduct
#print axioms exists_sourceReferenceTVOneRunCertificate_operationalColdHot_weightedProduct
#print axioms exists_sourceReferenceTVOneRunCertificate_operationalGaussianColdHot
#print axioms exists_sourceReferenceTVOneRunCertificate_operationalColdHot_sourceSharp
#print axioms radialLogSourcePublicReferenceTVCertificates_of_operationalColdHotAudit
#print axioms cvRadialLogExpectedImplementation_of_operationalColdHotAudits
#print axioms cvRadialLogExpectedImplementation_of_operationalColdHotOneRunCertificates

end Ttc.CVGaussianHybridWeightedCertificate
