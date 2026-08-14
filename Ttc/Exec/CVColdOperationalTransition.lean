import Ttc.Exec.CVColdOperationalPairTV
import Ttc.Exec.CVColdCrossPhaseWarm
import Ttc.Exec.CVIdealCombinedAccepted

/-!
# Operational cold transition/reference adapter

This module identifies the zero-safe operational cold phase's ideal accepted-score target
with the truncated Gaussian cooling law.  It then combines the resulting exact
`hphaseSeedTV` statement with the support-correct cross-phase warmth theorem.  The target
is therefore suitable both as the next heterogeneous seed reference and as the incoming
warm reference for the following radius-four phase.
-/

set_option autoImplicit false

namespace Ttc.CVColdOperationalTransition

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVCombinedContinuingAccept
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVColdOperationalKernel
open Ttc.CVColdOperationalPairTV
open Ttc.CVColdCrossPhaseWarm
open Ttc.CVCorrectedFixedBlockCost
open Ttc.CVSourceTruncatedFixedCost
open Ttc.CVHybridSchedule
open scoped ENNReal Classical

variable {n m : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

/-- Exact raw-seed reference produced by ideal acceptance in cold phase `i`. -/
noncomputable def coldIdealSeedReference
    (m n : Nat) (K : Set (State n)) (s0 : Real) (i : Nat) :
    Measure (State n) :=
  let c : Real := 1 - 1 / (2 * (n : Real))
  Measure.map (fun x : State n ↦ c • x)
    (coolLaw m (fixedSigmaSq n s0)
      (fixedRadiusFourBody K (fixedSigmaSq n s0 i)) i)

/-- The exact cold transition reference is a probability measure. -/
theorem isProbabilityMeasure_coldIdealSeedReference
    (hn : 1 ≤ n) (K : Set (State n))
    (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0) (i : Nat)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n) :
    IsProbabilityMeasure (coldIdealSeedReference m n K s0 i) := by
  let body := fixedRadiusFourBody K (fixedSigmaSq n s0 i)
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball hrad
  have hbodyTop : volume body ≠ ⊤ := volume_inter_closedBall_ne_top K _
  letI : IsProbabilityMeasure
      (coolLaw m (fixedSigmaSq n s0) body i) :=
    coolLaw_isProbabilityMeasure hsigma hbodyBall hbodyTop i
  unfold coldIdealSeedReference
  exact Measure.isProbabilityMeasure_map
    (measurable_const_smul (1 - 1 / (2 * (n : Real)))).aemeasurable

/-- The operational cold seed output is close to the exact truncated cooling reference.
The retry schedule may vary globally; only its value at the current phase is fixed by the
adjustable speedy deadline. -/
theorem tvLe_seed_bind_coldGaussianCostedKernel_coldIdealSeedReference
    (hn : 21 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat)
    (hi : i < m)
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
      (rho.bind (Kernel.map
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
      (coldIdealSeedReference m n K s0 i)
      (32 * zeta + (eta + Ttc.CVContinuingRetryParameters.continuingContraction ^ L)) := by
  have hn1 : 1 ≤ n := by omega
  let s := fixedSigmaSq n s0 i
  let delta := fixedRadiusFourDelta n s
  let body := fixedRadiusFourBody K s
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hsigma : ∀ j, 0 < fixedSigmaSq n s0 j := by
    intro j
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) j
  have hbodyM : MeasurableSet body := measurableSet_fixedRadiusFourBody hK _
  have hbodyC : Convex Real body := convex_fixedRadiusFourBody hKc _
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball hrad
  have hbodyTop : volume body ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hdelta : 0 < delta := by
    dsimp only [delta, s]
    exact fixedRadiusFourDelta_pos hn1 (hsigma i)
  have hdeltan : delta ≤ 1 / (2 * (n : Real)) := fixedRadiusFourDelta_le_n
  have hideal := Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw
    hn1 hsigma hbodyM hbodyC hbodyBall hbodyTop hdelta hdeltan hi
  have htv := tvLe_seed_bind_coldGaussianCostedKernel_adjustable_zeroSafe_of_eq
    hn K hK hKc hball s0 hs0 retrySteps retries i rho
      hM1 hMtop heta0 hetatop heta1 hzeta0 hzetatop hzeta16 hrad hwarm L
      hsteps hretries
  dsimp only at hideal htv
  rw [hideal] at htv
  simpa only [coldIdealSeedReference, body, delta, s, c] using htv

/-- The same ideal seed reference is an explicit warm start for the next radius-four
speedy stationary law. -/
theorem isWarm_coldIdealSeedReference_next
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (s0 : Real) (hs0 : 0 < s0) (i : Nat)
    (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n) :
    let c : Real := 1 - 1 / (2 * (n : Real))
    IsWarm
      (ENNReal.ofReal ((c⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2))
      (coldIdealSeedReference m n K s0 i)
      (ellGaussianProb
        (fixedRadiusFourBody K (fixedSigmaSq n s0 (i + 1)))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 (i + 1)))
        (fixedSigmaSq n s0 (i + 1))) := by
  dsimp only
  have hsnext : 0 < fixedSigmaSq n s0 (i + 1) := by
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  simpa only [coldIdealSeedReference] using
    (isWarm_standardScaledTruncated_ellGaussianProb_succ
      (m := m) hn hs0 hK hKc hball hfin hi hrad hradTwo
      (fixedRadiusFourDelta_pos hn hsnext) fixedRadiusFourDelta_le_n)

/-- Cold-to-hot boundary: the final truncated cold reference is warm for the first
full-body speedy stationary law. -/
theorem isWarm_coldIdealSeedReference_next_fullBody
    (hn : 1 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (s0 : Real) (hs0 : 0 < s0) (i : Nat)
    (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    {delta : Real} (hdelta : 0 < delta)
    (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    let c : Real := 1 - 1 / (2 * (n : Real))
    IsWarm
      (ENNReal.ofReal ((c⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2))
      (coldIdealSeedReference m n K s0 i)
      (ellGaussianProb K delta (fixedSigmaSq n s0 (i + 1))) := by
  dsimp only
  simpa only [coldIdealSeedReference] using
    (isWarm_standardScaledTruncated_full_ellGaussianProb_succ
      (m := m) hn hs0 hK hKc hball hfin hi hrad hradTwo hdelta hdeltan)

/-- The successor phase's operational query mean is bounded under the exact transition
reference.  Cross-phase warmth is discharged internally, so this is the cold successor
`hphaseCost` adapter required by the retained-history certificate. -/
theorem coldGaussian_referenceCost_le_coldIdealSeedReference_next
    (hn : 21 ≤ n) (K : Set (State n)) (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : State n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) (s0 : Real) (hs0 : 0 < s0)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat) (i : Nat)
    (hi : i + 1 < m)
    (hrad : 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : 1 ≤
      2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n) :
    let c : Real := 1 - 1 / (2 * (n : Real))
    let warmConstant : ENNReal :=
      ENNReal.ofReal ((c⁻¹) ^ n) *
        (ENNReal.ofReal (Real.exp (1 / 2)) * 2)
    (∫⁻ x, heterogeneousStepMean
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries (i + 1)) x
      ∂(coldIdealSeedReference m n K s0 i)) ≤
      ∑ j ∈ Finset.range (retries (i + 1)),
        10 * ((retrySteps (i + 1) j : ENNReal) * warmConstant) := by
  dsimp only
  let c : Real := 1 - 1 / (2 * (n : Real))
  let warmConstant : ENNReal :=
    ENNReal.ofReal ((c⁻¹) ^ n) *
      (ENNReal.ofReal (Real.exp (1 / 2)) * 2)
  let snext := fixedSigmaSq n s0 (i + 1)
  let deltaNext := fixedRadiusFourDelta n snext
  let bodyNext := fixedRadiusFourBody K snext
  have hn1 : 1 ≤ n := by omega
  have hsnext : 0 < snext := by
    dsimp only [snext]
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) (i + 1)
  have hradNext : 1 ≤ 4 * Real.sqrt snext * Real.sqrt n := by
    calc
      1 ≤ 2 * Real.sqrt snext * Real.sqrt n := by simpa only [snext] using hradTwo
      _ ≤ 4 * Real.sqrt snext * Real.sqrt n := by
        have hnon : 0 ≤ Real.sqrt snext * Real.sqrt n :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        nlinarith
  have hbodyM : MeasurableSet bodyNext := measurableSet_fixedRadiusFourBody hK _
  have hbodyC : Convex Real bodyNext := convex_fixedRadiusFourBody hKc _
  have hbodyBall : ball (0 : State n) 1 ⊆ bodyNext :=
    unitBall_subset_inter_closedBall hball hradNext
  have hbodyTop : volume bodyNext ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hdeltaNext : 0 < deltaNext := by
    dsimp only [deltaNext]
    exact fixedRadiusFourDelta_pos hn1 hsnext
  have hc0 : 0 < c := by
    dsimp only [c]
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn1
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp only [c]
    have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn1
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdeltaC : deltaNext ≤ 1 - c := by
    have hdeltan : deltaNext ≤ 1 / (2 * (n : Real)) := fixedRadiusFourDelta_le_n
    dsimp only [c]
    linarith
  have hM0 : ellGaussianMeasure bodyNext deltaNext snext Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hbodyM hbodyC hbodyBall
      hc0 hc1 hdeltaNext hdeltaC hsnext
  have hMtop : ellGaussianMeasure bodyNext deltaNext snext Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hsnext bodyNext deltaNext hbodyTop
  letI : IsProbabilityMeasure
      (coldIdealSeedReference m n K s0 i) :=
    isProbabilityMeasure_coldIdealSeedReference hn1 K hball s0 hs0 i hrad
  letI : IsProbabilityMeasure (ellGaussianProb bodyNext deltaNext snext) :=
    isProbabilityMeasure_ellGaussianProb hM0 hMtop
  have hwarm : IsWarm warmConstant
      (coldIdealSeedReference m n K s0 i)
      (ellGaussianProb bodyNext deltaNext snext) := by
    simpa only [warmConstant, c, bodyNext, deltaNext, snext] using
      (isWarm_coldIdealSeedReference_next
        (m := m) hn1 K hK hKc hball hfin s0 hs0 i hi hrad hradTwo)
  simpa only [warmConstant, bodyNext, deltaNext, snext] using
    (coldGaussian_referenceCost_le_of_warm
      (by omega : 2 ≤ n) K hK hKc hball s0 hs0 retrySteps retries
      (coldIdealSeedReference m n K s0 i) warmConstant (i + 1)
      hradNext hwarm)

/-! ## Phase-indexed reference schedule -/

/-- Explicit universal cross-phase warmness constant for successor cold phases. -/
noncomputable def coldSuccessorWarmConstant (n : Nat) : ENNReal :=
  let c : Real := 1 - 1 / (2 * (n : Real))
  ENNReal.ofReal ((c⁻¹) ^ n) *
    (ENNReal.ofReal (Real.exp (1 / 2)) * 2)

/-- The cold reference begins at the supplied initial seed law and thereafter uses the
exact ideal seed law produced by the preceding phase. -/
noncomputable def coldOperationalReferenceSchedule
    (initial : Measure (State n)) (m : Nat) (K : Set (State n)) (s0 : Real) :
    Nat → Measure (State n)
  | 0 => initial
  | i + 1 => coldIdealSeedReference m n K s0 i

/-- Initial warmth may differ; every successor uses the explicit cross-phase constant. -/
noncomputable def coldOperationalWarmSchedule (M0 : ENNReal) (n : Nat) :
    Nat → ENNReal
  | 0 => M0
  | _ + 1 => coldSuccessorWarmConstant n

/-- Genuine phase-indexed adjustable retry policy used by the operational cold kernel. -/
noncomputable def coldOperationalAdjustableRetrySteps
    (n : Nat) (s0 : Real) (M eta zeta : Nat → ENNReal) : Nat → Nat → Nat :=
  fun i _ ↦ Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
    (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
    (fixedSigmaSq n s0 i) (M i / eta i) (zeta i)

theorem isProbabilityMeasure_coldOperationalReferenceSchedule
    (hn : 1 ≤ n) (initial : Measure (State n)) [IsProbabilityMeasure initial]
    (K : Set (State n)) (hball : ball (0 : State n) 1 ⊆ K)
    (s0 : Real) (hs0 : 0 < s0)
    (hrad : ∀ i, 1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (i : Nat) :
    IsProbabilityMeasure (coldOperationalReferenceSchedule initial m K s0 i) := by
  cases i with
  | zero => simpa only [coldOperationalReferenceSchedule] using
      (inferInstance : IsProbabilityMeasure initial)
  | succ i =>
      simpa only [coldOperationalReferenceSchedule] using
        (isProbabilityMeasure_coldIdealSeedReference
          (m := m) hn K hball s0 hs0 i (hrad i))

/-- Every active reference in the explicit schedule is warm for its own phase's
radius-four speedy stationary law: phase zero by the supplied premise, successors by the
machine-checked changing-body comparison. -/
theorem isWarm_coldOperationalReferenceSchedule
    (hn : 1 ≤ n) (initial : Measure (State n))
    (K : Set (State n)) (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (s0 : Real) (hs0 : 0 < s0) (M0 : ENNReal)
    (hwarm0 : IsWarm M0 initial
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 0))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 0))
        (fixedSigmaSq n s0 0)))
    (hrad : ∀ i, i < m →
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : ∀ i, i + 1 < m →
      1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    (i : Nat) (hi : i < m) :
    IsWarm (coldOperationalWarmSchedule M0 n i)
      (coldOperationalReferenceSchedule initial m K s0 i)
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 i))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 i))
        (fixedSigmaSq n s0 i)) := by
  cases i with
  | zero => simpa only [coldOperationalWarmSchedule,
      coldOperationalReferenceSchedule] using hwarm0
  | succ i =>
      simpa only [coldOperationalWarmSchedule, coldOperationalReferenceSchedule,
        coldSuccessorWarmConstant] using
        (isWarm_coldIdealSeedReference_next
          (m := m) hn K hK hKc hball hfin s0 hs0 i hi
          (hrad i (by omega)) (hradTwo i hi))

/-- Exact active-cold `hphaseSeedTV` family for the retained-history certificate.  Both
the incoming warmth and the successor target identification are internal. -/
theorem tvLe_coldOperationalReferenceSchedule_phase
    (hn : 21 ≤ n) (initial : Measure (State n))
    (K : Set (State n)) (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (s0 : Real) (hs0 : 0 < s0) (M0 : ENNReal)
    [∀ i, IsProbabilityMeasure
      (coldOperationalReferenceSchedule initial m K s0 i)]
    (eta zeta : Nat → ENNReal) (retries : Nat → Nat)
    (hwarm0 : IsWarm M0 initial
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 0))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 0))
        (fixedSigmaSq n s0 0)))
    (hM1 : ∀ i, i < m → 1 ≤ coldOperationalWarmSchedule M0 n i)
    (hMtop : ∀ i, i < m → coldOperationalWarmSchedule M0 n i ≠ ⊤)
    (heta0 : ∀ i, i < m → eta i ≠ 0)
    (hetatop : ∀ i, i < m → eta i ≠ ⊤)
    (heta1 : ∀ i, i < m → eta i ≤ 1)
    (hzeta0 : ∀ i, i < m → zeta i ≠ 0)
    (hzetatop : ∀ i, i < m → zeta i ≠ ⊤)
    (hzeta16 : ∀ i, i < m → zeta i ≤ ENNReal.ofReal (1 / 16 : Real))
    (hrad : ∀ i, i < m →
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : ∀ i, i + 1 < m →
      1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    (i : Nat) (hi : i < m) :
    TVLe
      ((coldOperationalReferenceSchedule initial m K s0 i).bind
        (Kernel.map
          (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
            (coldOperationalAdjustableRetrySteps n s0
              (coldOperationalWarmSchedule M0 n) eta zeta)
            retries i)
          (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
      (coldOperationalReferenceSchedule initial m K s0 (i + 1))
      (32 * zeta i + (eta i +
        Ttc.CVContinuingRetryParameters.continuingContraction ^ retries i)) := by
  have hwarm := isWarm_coldOperationalReferenceSchedule
    (m := m) (by omega : 1 ≤ n) initial K hK hKc hball hfin s0 hs0 M0 hwarm0
      hrad hradTwo i hi
  simpa only [coldOperationalReferenceSchedule] using
    (tvLe_seed_bind_coldGaussianCostedKernel_coldIdealSeedReference
      (m := m) hn K hK hKc hball s0 hs0
      (coldOperationalAdjustableRetrySteps n s0
        (coldOperationalWarmSchedule M0 n) eta zeta)
      retries i hi (coldOperationalReferenceSchedule initial m K s0 i)
      (hM1 i hi) (hMtop i hi) (heta0 i hi) (hetatop i hi) (heta1 i hi)
      (hzeta0 i hi) (hzetatop i hi) (hzeta16 i hi) (hrad i hi) hwarm
      (retries i) rfl rfl)

/-- Exact active-cold `hphaseCost` family for the same reference schedule.  The phase-zero
warm premise and every successor cross-phase warm comparison are discharged uniformly. -/
theorem coldGaussian_referenceCost_le_coldOperationalReferenceSchedule_phase
    (hn : 21 ≤ n) (initial : Measure (State n))
    (K : Set (State n)) (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (s0 : Real) (hs0 : 0 < s0) (M0 : ENNReal)
    (retrySteps : Nat → Nat → Nat) (retries : Nat → Nat)
    [∀ i, IsProbabilityMeasure
      (coldOperationalReferenceSchedule initial m K s0 i)]
    (hwarm0 : IsWarm M0 initial
      (ellGaussianProb (fixedRadiusFourBody K (fixedSigmaSq n s0 0))
        (fixedRadiusFourDelta n (fixedSigmaSq n s0 0))
        (fixedSigmaSq n s0 0)))
    (hrad : ∀ i, i < m →
      1 ≤ 4 * Real.sqrt (fixedSigmaSq n s0 i) * Real.sqrt n)
    (hradTwo : ∀ i, i + 1 < m →
      1 ≤ 2 * Real.sqrt (fixedSigmaSq n s0 (i + 1)) * Real.sqrt n)
    (i : Nat) (hi : i < m) :
    (∫⁻ x, heterogeneousStepMean
        (coldGaussianCostedKernel (by omega : 1 ≤ n) K hK s0 hs0
          retrySteps retries i) x
      ∂(coldOperationalReferenceSchedule initial m K s0 i)) ≤
      ∑ j ∈ Finset.range (retries i),
        10 * ((retrySteps i j : ENNReal) *
          coldOperationalWarmSchedule M0 n i) := by
  let s := fixedSigmaSq n s0 i
  let delta := fixedRadiusFourDelta n s
  let body := fixedRadiusFourBody K s
  have hn1 : 1 ≤ n := by omega
  have hs : 0 < s := by
    dsimp only [s]
    unfold fixedSigmaSq
    exact geomSchedule_pos hs0 (by positivity) i
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact fixedRadiusFourDelta_pos hn1 hs
  have hbodyM : MeasurableSet body := measurableSet_fixedRadiusFourBody hK _
  have hbodyC : Convex Real body := convex_fixedRadiusFourBody hKc _
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball (hrad i hi)
  have hbodyTop : volume body ≠ ⊤ := volume_inter_closedBall_ne_top K _
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    dsimp only [c]
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn1
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hc1 : c < 1 := by
    dsimp only [c]
    have hnR : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn1
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdeltaC : delta ≤ 1 - c := by
    have hdeltan : delta ≤ 1 / (2 * (n : Real)) := fixedRadiusFourDelta_le_n
    dsimp only [c]
    linarith
  have hM0 : ellGaussianMeasure body delta s Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero_of_ball hbodyM hbodyC hbodyBall
      hc0 hc1 hdelta hdeltaC hs
  have hMtop : ellGaussianMeasure body delta s Set.univ ≠ ⊤ :=
    ellGaussianMeasure_univ_ne_top hs body delta hbodyTop
  letI : IsProbabilityMeasure (ellGaussianProb body delta s) :=
    isProbabilityMeasure_ellGaussianProb hM0 hMtop
  have hwarm := isWarm_coldOperationalReferenceSchedule
    (m := m) hn1 initial K hK hKc hball hfin s0 hs0 M0 hwarm0
      hrad hradTwo i hi
  simpa only [body, delta, s] using
    (coldGaussian_referenceCost_le_of_warm
      (by omega : 2 ≤ n) K hK hKc hball s0 hs0 retrySteps retries
      (coldOperationalReferenceSchedule initial m K s0 i)
      (coldOperationalWarmSchedule M0 n i) i (hrad i hi) hwarm)

#print axioms tvLe_seed_bind_coldGaussianCostedKernel_coldIdealSeedReference
#print axioms isWarm_coldIdealSeedReference_next
#print axioms isWarm_coldIdealSeedReference_next_fullBody
#print axioms coldGaussian_referenceCost_le_coldIdealSeedReference_next
#print axioms tvLe_coldOperationalReferenceSchedule_phase
#print axioms coldGaussian_referenceCost_le_coldOperationalReferenceSchedule_phase

end Ttc.CVColdOperationalTransition
