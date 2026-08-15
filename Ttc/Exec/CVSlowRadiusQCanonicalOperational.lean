import Ttc.Exec.CVSlowRadiusQRecursiveOperational
import Ttc.Exec.CVGaussianScoreAwareParameters
import Ttc.Exec.CVHybridRadiusQOperationalLocalPair

/-! Canonical score-aware operation for the uniformly slow schedule. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Ttc.CVSlowRadiusQCanonicalOperational

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVSequentialPhaseSampler
open Ttc.CVSeedProjectedDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianScoreSeedPhaseKernel
open Ttc.CVWarmBudgetRecurrence Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVSlowRadiusQRecursiveOperational Ttc.CVSlowRadiusQOperationalPair
open Ttc.CVSlowRadiusQFallbackSchedule
open Ttc.CVSlowRadiusQReferencePhaseTV Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVAdaptiveRadiusQPrimitives Ttc.CVGaussianAdaptiveMixing
open Ttc.CVContinuingRetryParameters Ttc.CVGaussianScoreAwareParameters
open Ttc.CVHybridRadiusQOperationalLocalPair
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def slowWarmBudget
    (initialWarm : ENNReal) (n : Nat) (q s0 : Real) (K : Set (State n))
    (retries : Nat → Nat) : Nat → ENNReal :=
  recursiveWarmBudget initialWarm (slowAcceptedFactor retries)
    (slowFallbackFactor n q s0 K)

noncomputable def slowCanonicalSteps
    (initialWarm : ENNReal) (n : Nat) (q s0 : Real) (K : Set (State n))
    (retries : Nat → Nat) (etaShare zetaShare : Nat → ENNReal) : Nat → Nat → Nat :=
  fun i _ ↦ adjustableSpeedyDeadline n
    (radiusQDelta n q (slowSourceSigmaSq n s0 i)) (slowSourceSigmaSq n s0 i)
    ((2 * slowWarmBudget initialWarm n q s0 K retries i) / etaShare i)
    (zetaShare i)

noncomputable def slowLocalPairReference
    (m n : Nat) (q s0 : Real) (K : Set (State n)) (i : Nat) :
    Measure (ScoreSeed n) :=
  scoreSeedReference (1 - 1 / (2 * (n : Real)))
    (coolLaw m (slowSourceSigmaSq n s0)
      (radiusQBody q K (slowSourceSigmaSq n s0 i)) i)

theorem isProbabilityMeasure_slowLocalPairReference
    (hn : 1 ≤ n) (m : Nat) {q s0 : Real} (hs0 : 0 < s0)
    (K : Set (State n)) (hball : ball (0 : State n) 1 ⊆ K)
    (i : Nat) (hrad : 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n) :
    IsProbabilityMeasure (slowLocalPairReference m n q s0 K i) := by
  unfold slowLocalPairReference scoreSeedReference
  let body := radiusQBody q K (slowSourceSigmaSq n s0 i)
  have hbodyBall : ball (0 : State n) 1 ⊆ body :=
    unitBall_subset_inter_closedBall hball
      (by simpa only [body, radiusQBody] using hrad)
  have hbodyTop : volume body ≠ ⊤ := by
    dsimp only [body, radiusQBody]
    exact volume_inter_closedBall_ne_top K _
  letI : IsProbabilityMeasure (coolLaw m (slowSourceSigmaSq n s0) body i) :=
    coolLaw_isProbabilityMeasure (slowSourceSigmaSq_pos hn hs0) hbodyBall hbodyTop i
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The actual slow path is operational with local graph targets.  The radial tail is
deliberately not charged here; it is supplied to the robust estimator as target TV. -/
noncomputable def seedProjectedOperational_slowRadiusQ_scoreAware
    (hn : 21 ≤ n) (m k : Nat) (hk : 1 ≤ k)
    {q s0 eps : Real} (hq : 1 < q) (hs0 : 0 < s0)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hrad : ∀ i,
      1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n)
    (scoreScale : Real) {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i)
    (tail : Nat → Measure (ScoreSeed n)) [∀ i, IsProbabilityMeasure (tail i)]
    (mu0 : Measure (ScoreSeed n)) [IsProbabilityMeasure mu0]
    (V : Nat → (Nat → ScoreSeed n) → Real)
    (initialWarm : ENNReal) (hinitialOne : 1 ≤ initialWarm)
    (hinitialTop : initialWarm ≠ ⊤)
    (hstart : IsWarm initialWarm (Measure.map Prod.snd mu0)
      (slowRadiusQSeedTarget n q s0 K 0))
    (htailSeed : ∀ i, Measure.map Prod.snd (tail i) = slowRadiusQSeedTarget n q s0 K i)
    (u : (i : Nat) → (Finset.Iic i → ScoreSeed n) → Real)
    (v : Nat → State n → Real)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
    (hU : ∀ i, accuracyU
      (inhomogeneousPathMeasure (stateScheduleFromSeed
        (activeReferenceTailSchedule m
          (slowWarmFallbackSchedule (by omega : 1 ≤ n) q (zero_lt_one.trans hq) hs0
            K hK
            (slowCanonicalSteps initialWarm n q s0 K
              (scoreAwareRetries m k eps slack boundSq)
              (scoreAwareEta m k eps slack boundSq)
              (scoreAwareZeta m k eps slack boundSq))
            (scoreAwareRetries m k eps slack boundSq) scoreScale) tail)) mu0)
      V (correctedAlpha m eps) i = fun omega ↦ u i (Preorder.frestrictLe i omega))
    (hV : ∀ i, V (i + 1) = fun omega ↦ v i (omega (i + 1)).1) :
    SeedProjectedOperational
      (stateScheduleFromSeed (activeReferenceTailSchedule m
        (slowWarmFallbackSchedule (by omega : 1 ≤ n) q (zero_lt_one.trans hq) hs0 K hK
          (slowCanonicalSteps initialWarm n q s0 K
            (scoreAwareRetries m k eps slack boundSq)
            (scoreAwareEta m k eps slack boundSq)
            (scoreAwareZeta m k eps slack boundSq))
          (scoreAwareRetries m k eps slack boundSq) scoreScale) tail))
      (activeReferenceTailSchedule m
        (slowWarmFallbackSchedule (by omega : 1 ≤ n) q (zero_lt_one.trans hq) hs0 K hK
          (slowCanonicalSteps initialWarm n q s0 K
            (scoreAwareRetries m k eps slack boundSq)
            (scoreAwareEta m k eps slack boundSq)
            (scoreAwareZeta m k eps slack boundSq))
          (scoreAwareRetries m k eps slack boundSq) scoreScale) tail)
      Prod.snd Prod.fst mu0 V m eps := by
  let hn1 : 1 ≤ n := by omega
  let hq0 : 0 < q := zero_lt_one.trans hq
  let retries := scoreAwareRetries m k eps slack boundSq
  let etaShare := scoreAwareEta m k eps slack boundSq
  let zetaShare := scoreAwareZeta m k eps slack boundSq
  let steps := slowCanonicalSteps initialWarm n q s0 K retries etaShare zetaShare
  let warm := slowWarmBudget initialWarm n q s0 K retries
  let mixError := activeReferenceMixError m (scoreAwareMixError m k eps slack boundSq)
  letI : ∀ j, IsProbabilityMeasure (slowRadiusQFallback n s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_slowRadiusQFallback hn1 hs0 scoreScale j
  letI : ∀ i, IsProbabilityMeasure (slowLocalPairReference m n q s0 K i) := fun i ↦
    isProbabilityMeasure_slowLocalPairReference hn1 m hs0 K hball i
      (hrad i)
  apply seedProjectedOperational_slowRadiusQ_recursive hn1 m hq0 hs0 hK hKc hball hfin
    (fun i _ ↦ hrad i) steps retries scoreScale tail mu0 V eps
    (slowLocalPairReference m n q s0 K) initialWarm hinitialOne hstart htailSeed mixError
  · intro i hi
    unfold mixError activeReferenceMixError
    simp only [if_pos hi]
    exact scoreAwareMixError_ne_top m k eps slack boundSq i
  · intro i hi rho hwarm hprob
    letI : IsProbabilityMeasure rho := hprob
    have hrecOne : 1 ≤ warm i := one_le_recursiveWarmBudget hinitialOne
      (one_le_slowAcceptedFactor retries) i
    have hrecTop : warm i ≠ ⊤ := recursiveWarmBudget_ne_top hinitialTop
      (fun j ↦ by
        unfold slowAcceptedFactor
        finiteness)
      (slowFallbackFactor_ne_top hn1 hs0 hK) i
    have hM1 : 1 ≤ 2 * warm i := hrecOne.trans
      (le_mul_of_one_le_left' (by norm_num))
    have hMtop : 2 * warm i ≠ ⊤ := ENNReal.mul_ne_top (by simp) hrecTop
    have heta0 : etaShare i ≠ 0 := by
      exact ENNReal.ofReal_ne_zero_iff.mpr
        (scoreAwareShare_pos heps hslack hbound i)
    have hzeta0 : zetaShare i ≠ 0 := by
      exact ENNReal.ofReal_ne_zero_iff.mpr
        (div_pos (scoreAwareShare_pos heps hslack hbound i) (by norm_num))
    have hpair :=
      Ttc.CVSlowRadiusQOperationalPair.tvLe_radiusQWarmFallbackKernelOfSigma_localPair_adjustable_zeroSafe_of_eq
        (m := m) hn hq (slowSourceSigmaSq n s0) (slowSourceSigmaSq_pos hn1 hs0)
        hK hKc hball steps retries (slowRadiusQFallback n s0 scoreScale)
        i (Nat.lt_of_succ_lt hi) rho hM1 hMtop
        heta0 ENNReal.ofReal_ne_top
        (by
          change ENNReal.ofReal (scoreAwareShare m k eps slack boundSq i) ≤ 1
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (scoreAwareShare_lt_one heps heps1 i).le)
        hzeta0 ENNReal.ofReal_ne_top (scoreAwareZeta_le_sixteenth heps heps1 i)
        (hrad i)
        (by simpa only [warm, slowWarmBudget, slowRadiusQSeedTarget] using hwarm)
        (retries i) (by rfl) rfl
    simpa only [slowWarmFallbackSchedule, mixError, activeReferenceMixError,
      if_pos hi, retries, etaShare, zetaShare, slowLocalPairReference,
      scoreAwareMixError] using hpair
  · exact hu
  · exact hv
  · simpa only [steps, retries, etaShare, zetaShare] using hU
  · exact hV
  · intro i hi
    unfold mixError activeReferenceMixError
    simp only [if_pos hi]
    have hb := scoreAwareMixError_budget (m := m) (k := k)
      heps heps1 hslack hbound i
    have hk0 : (0 : Real) ≤ k := by positivity
    have hlocal0 : 0 ≤ 2 * (scoreAwareMixError m k eps slack boundSq i).toReal := by positivity
    calc
      2 * (scoreAwareMixError m k eps slack boundSq i).toReal =
          1 * (2 * (scoreAwareMixError m k eps slack boundSq i).toReal) := by ring
      _ ≤ (k : Real) * (2 * (scoreAwareMixError m k eps slack boundSq i).toReal) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hlocal0
      _ ≤ correctedNu m eps := hb

#print axioms seedProjectedOperational_slowRadiusQ_scoreAware

end Ttc.CVSlowRadiusQCanonicalOperational
