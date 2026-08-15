import Ttc.Exec.CVSlowRadiusQReferenceCost
import Ttc.Exec.CVRelativeWeightedRetainedCertificate
import Ttc.Exec.CVGaussianCappedCostedSchedule
import Ttc.Exec.CVGaussianScoreAwareParameters
import Ttc.Exec.CVSlowGlobalRadiusTailBudget

/-! A retained-reference certificate seam for the honest uniformly slow schedule.

All phase distribution and phase expected-cost obligations are discharged here.  The
only remaining premises of the capstone theorem are aggregate scalar accounting and
the weighted estimator's ordinary-path accuracy. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Ttc.CVSlowSourceReferenceCertificate

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.Probability Arlib.MarkovChains
open Arlib.GaussianCooling Arlib.GaussianCooling.Chunked
open Ttc.CVSequentialPhaseSampler Ttc.CVAdaptiveRadiusQPrimitives
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowRadiusQFallbackSchedule
open Ttc.CVSlowRadiusQReferencePhaseTV Ttc.CVSlowRadiusQReferenceCost
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVGaussianCappedCostedSchedule Ttc.CVHeterogeneousHistoryReference
open Ttc.CVHeterogeneousRetainedPathLaw Ttc.CVRelativeWeightedRetainedCertificate
open Ttc.CVSourceReferenceTVCapstone Ttc.CVIndependentRefreshSeedLaws
open Ttc.CVIndependentStreamDependence
open Ttc.CVScoreSeedPhaseKernel
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open Ttc.CVSlowGlobalRadiusTailBudget
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def slowSourceInitialVariance (n : Nat) : Real :=
  1 / (16 * (n : Real))

noncomputable def slowReferenceWarm : ENNReal :=
  ENNReal.ofReal (2 * Real.exp 1)

noncomputable def slowScoreAwareSteps
    (n m k : Nat) (q eps : Real) (slack boundSq : Nat → Real) : Nat → Nat → Nat :=
  fun i _ ↦ Ttc.CVGaussianAdaptiveMixing.adjustableSpeedyDeadline n
    (radiusQDelta n q (slowSourceSigmaSq n (slowSourceInitialVariance n) i))
    (slowSourceSigmaSq n (slowSourceInitialVariance n) i)
    (slowReferenceWarm / scoreAwareEta m k eps slack boundSq i)
    (scoreAwareZeta m k eps slack boundSq i)

noncomputable def slowRawSchedule
    (hn : 1 ≤ n) (m k : Nat) (q eps : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (scoreScale : Real) :
    Nat → Kernel (State n) (ScoreSeed n) := by
  letI : ∀ i, IsProbabilityMeasure
      (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale i) := fun i ↦
    isProbabilityMeasure_slowRadiusQFallback hn
      (by unfold slowSourceInitialVariance; positivity) scoreScale i
  exact radiusQWarmFallbackKernelOfSigma hn q hq K hK
    (slowSourceSigmaSq n (slowSourceInitialVariance n))
    (slowSourceSigmaSq_pos hn (by unfold slowSourceInitialVariance; positivity))
    (slowScoreAwareSteps n m k q eps slack boundSq)
    (scoreAwareRetries m k eps slack boundSq)
    (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale)

noncomputable def slowRawCostedSchedule
    (hn : 1 ≤ n) (m k : Nat) (q eps : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (scoreScale : Real) :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) := by
  letI : ∀ i, IsProbabilityMeasure
      (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale i) := fun i ↦
    isProbabilityMeasure_slowRadiusQFallback hn
      (by unfold slowSourceInitialVariance; positivity) scoreScale i
  exact radiusQWarmFallbackCostedKernelOfSigma hn q hq K hK
    (slowSourceSigmaSq n (slowSourceInitialVariance n))
    (slowSourceSigmaSq_pos hn (by unfold slowSourceInitialVariance; positivity))
    (slowScoreAwareSteps n m k q eps slack boundSq)
    (scoreAwareRetries m k eps slack boundSq)
    (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale)

instance slowRawSchedule.isMarkovKernel
    (hn : 1 ≤ n) (m k : Nat) (q eps : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (scoreScale : Real) (i : Nat) :
    IsMarkovKernel (slowRawSchedule hn m k q eps hq K hK slack boundSq scoreScale i) := by
  unfold slowRawSchedule
  infer_instance

instance slowRawCostedSchedule.isMarkovKernel
    (hn : 1 ≤ n) (m k : Nat) (q eps : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (scoreScale : Real) (i : Nat) :
    IsMarkovKernel
      (slowRawCostedSchedule hn m k q eps hq K hK slack boundSq scoreScale i) := by
  unfold slowRawCostedSchedule
  infer_instance

noncomputable def slowInitialSeed (n : Nat) : Measure (State n) :=
  coldBallStart (n := n) (slowSourceInitialVariance n)
    (coldRefreshRadius n (slowSourceInitialVariance n))

noncomputable def slowRetainedSeedTarget
    (m n : Nat) (q : Real) (K : Set (State n)) : Nat → Measure (State n)
  | 0 => slowInitialSeed n
  | i + 1 => slowRadiusQLocalGraphSeedTarget m n q
      (slowSourceInitialVariance n) K i

noncomputable def slowInitialPair (n : Nat) : Measure (ScoreSeed n) :=
  Measure.map (fun y : State n ↦ ((0 : State n), y)) (slowInitialSeed n)

noncomputable def slowExactTail
    (m n : Nat) (q : Real) (K : Set (State n)) (i : Nat) : Measure (ScoreSeed n) :=
  Measure.map (fun y : State n ↦ ((0 : State n), y))
    (slowRetainedSeedTarget m n q K i)

theorem map_snd_slowInitialPair (n : Nat) :
    Measure.map Prod.snd (slowInitialPair n) = slowInitialSeed n := by
  unfold slowInitialPair
  rw [Measure.map_map measurable_snd (by fun_prop)]
  exact Measure.map_id

theorem map_snd_slowExactTail (m n : Nat) (q : Real) (K : Set (State n)) (i : Nat) :
    Measure.map Prod.snd (slowExactTail m n q K i) =
      slowRetainedSeedTarget m n q K i := by
  unfold slowExactTail
  rw [Measure.map_map measurable_snd (by fun_prop)]
  exact Measure.map_id

theorem coldRefreshRadius_initial_eq_half
    (hn : 1 ≤ n) :
    coldRefreshRadius n (slowSourceInitialVariance n) = 1 / 2 := by
  have hs0 : 0 < slowSourceInitialVariance n := by
    unfold slowSourceInitialVariance
    positivity
  have hr0 := coldRefreshRadius_pos hn hs0
  have hrsq := coldRefreshRadius_sq hn hs0
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hsimp : 4 * (n : Real) * slowSourceInitialVariance n = 1 / 4 := by
    unfold slowSourceInitialVariance
    field_simp
    ring
  rw [hsimp] at hrsq
  nlinarith

theorem isProbabilityMeasure_slowInitialSeed
    (hn : 1 ≤ n) : IsProbabilityMeasure (slowInitialSeed n) := by
  have hs0 : 0 < slowSourceInitialVariance n := by
    unfold slowSourceInitialVariance
    positivity
  unfold slowInitialSeed
  exact isProbabilityMeasure_gaussianBallRefresh hs0 (coldRefreshRadius_pos hn hs0)

theorem isProbabilityMeasure_slowRetainedSeedTarget
    (hn : 1 ≤ n) {m : Nat} {q : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hball : ball (0 : State n) 1 ⊆ K) (i : Nat) :
    IsProbabilityMeasure (slowRetainedSeedTarget m n q K i) := by
  cases i with
  | zero => exact isProbabilityMeasure_slowInitialSeed hn
  | succ i =>
      exact isProbabilityMeasure_slowRadiusQLocalGraphSeedTarget hn m
        (by unfold slowSourceInitialVariance; positivity) hball i
        (one_le_slow_radius hn hq4 (by rfl) i)

theorem isWarm_slowRetainedSeedTarget
    (hn : 2 ≤ n) {m : Nat} {q : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    {i : Nat} (hi : i < m) :
    IsWarm slowReferenceWarm (slowRetainedSeedTarget m n q K i)
      (slowRadiusQSeedTarget n q (slowSourceInitialVariance n) K i) := by
  cases i with
  | zero =>
      have hs0 : 0 < slowSourceInitialVariance n := by
        unfold slowSourceInitialVariance; positivity
      let body := radiusQBody q K (slowSourceInitialVariance n)
      have hrad0 : 1 ≤ q * Real.sqrt (slowSourceInitialVariance n) * Real.sqrt n := by
        have hrad := one_le_slow_radius (by omega : 1 ≤ n) hq4 (by rfl) 0
        simpa only [slowSourceSigmaSq, Arlib.GaussianCooling.geomSchedule_zero,
          slowSourceInitialVariance] using hrad
      have hbodyBall : ball (0 : State n) 1 ⊆ body :=
        unitBall_subset_inter_closedBall hball
          (by simpa only [body, radiusQBody] using hrad0)
      have hc0 : 0 < 1 - 1 / (2 * (n : Real)) := by
        have hnR : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        linarith
      have hc1 : 1 - 1 / (2 * (n : Real)) < 1 := by
        have hn0 : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
        have : 0 < 1 / (2 * (n : Real)) := by positivity
        linarith
      have hfit : coldRefreshRadius n (slowSourceInitialVariance n) <
          1 - 1 / (2 * (n : Real)) := by
        rw [coldRefreshRadius_initial_eq_half (by omega : 1 ≤ n)]
        have hnR : (2 : Real) ≤ n := by exact_mod_cast hn
        have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        linarith
      have hw := isWarm_coldRefresh_ellGaussianProb (by omega : 1 ≤ n)
        (measurableSet_radiusQBody hK) (convex_radiusQBody hKc) hbodyBall hs0
        hc0 hc1 hfit
        (radiusQDelta_pos (by omega : 1 ≤ n) (lt_of_lt_of_le (by norm_num) hq4) hs0)
        (by simpa using radiusQDelta_le_n n q (slowSourceInitialVariance n))
      have htwo : (ENNReal.ofReal 2) ≤ slowReferenceWarm := by
          unfold slowReferenceWarm
          apply ENNReal.ofReal_le_ofReal
          nlinarith [Real.one_le_exp (show (0 : Real) ≤ 1 by norm_num)]
      have hw' : IsWarm (ENNReal.ofReal 2) (slowRetainedSeedTarget m n q K 0)
          (slowRadiusQSeedTarget n q (slowSourceInitialVariance n) K 0) := by
        simpa only [slowRetainedSeedTarget, slowInitialSeed,
          slowRadiusQSeedTarget, slowSourceSigmaSq,
          Arlib.GaussianCooling.geomSchedule_zero, body] using hw
      exact hw'.mono htwo
  | succ j =>
      simpa only [slowRetainedSeedTarget, slowReferenceWarm] using
        isWarm_slowRadiusQLocalGraphSeedTarget_succ_two_exp (by omega : 1 ≤ n)
          (lt_of_lt_of_le (by norm_num) hq4)
          (by unfold slowSourceInitialVariance; positivity) hK hKc hball
          (i := j) (by omega) (one_le_slow_radius (by omega : 1 ≤ n) hq4 (by rfl) j)

noncomputable def slowActiveSchedule
    (hn : 1 ≤ n) (m k : Nat) (q eps : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (scoreScale : Real) :
    Nat → Kernel (State n) (ScoreSeed n) :=
  activeReferenceTailSchedule m
    (slowRawSchedule hn m k q eps hq K hK slack boundSq scoreScale)
    (slowExactTail m n q K)

noncomputable def slowActiveCostedSchedule
    (hn : 1 ≤ n) (m k : Nat) (q eps : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (scoreScale : Real) :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) :=
  costedActiveReferenceTailSchedule m
    (slowRawCostedSchedule hn m k q eps hq K hK slack boundSq scoreScale)
    (slowExactTail m n q K)

instance slowActiveSchedule.isMarkovKernel
    (hn : 1 ≤ n) (m k : Nat) (q eps : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (scoreScale : Real)
    [∀ j, IsProbabilityMeasure (slowExactTail m n q K j)] (i : Nat) :
    IsMarkovKernel
      (slowActiveSchedule hn m k q eps hq K hK slack boundSq scoreScale i) := by
  unfold slowActiveSchedule
  infer_instance

instance slowActiveCostedSchedule.isMarkovKernel
    (hn : 1 ≤ n) (m k : Nat) (q eps : Real) (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (scoreScale : Real)
    [∀ j, IsProbabilityMeasure (slowExactTail m n q K j)] (i : Nat) :
    IsMarkovKernel
      (slowActiveCostedSchedule hn m k q eps hq K hK slack boundSq scoreScale i) := by
  unfold slowActiveCostedSchedule
  infer_instance

noncomputable def slowPhaseError
    (m k : Nat) (eps : Real) (slack boundSq : Nat → Real) : Nat → ENNReal :=
  activeReferenceMixError m (scoreAwareMixError m k eps slack boundSq)

noncomputable def slowPhaseCostBound
    (n m k : Nat) (q eps : Real) (slack boundSq : Nat → Real) : Nat → ENNReal :=
  fun i ↦ if i + 1 < m then
    ENNReal.ofReal (retryReferenceMeanEnvelope (2 * Real.exp 1)
      (slowScoreAwareSteps n m k q eps slack boundSq i)
      (scoreAwareRetries m k eps slack boundSq i)) else 0

theorem map_snd_slowRawCostedSchedule
    (hn : 1 ≤ n) (m k : Nat) {q eps : Real} (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (scoreScale : Real) (i : Nat) (x : State n) :
    Measure.map Prod.snd
        (slowRawCostedSchedule hn m k q eps hq K hK slack boundSq scoreScale i x) =
      slowRawSchedule hn m k q eps hq K hK slack boundSq scoreScale i x := by
  letI : ∀ j, IsProbabilityMeasure
      (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale j) := fun j ↦
    isProbabilityMeasure_slowRadiusQFallback hn
      (by unfold slowSourceInitialVariance; positivity) scoreScale j
  unfold slowRawCostedSchedule slowRawSchedule
  exact map_snd_radiusQWarmFallbackCostedKernelOfSigma hn q hq K hK
    (slowSourceSigmaSq n (slowSourceInitialVariance n))
    (slowSourceSigmaSq_pos hn (by unfold slowSourceInitialVariance; positivity))
    (slowScoreAwareSteps n m k q eps slack boundSq)
    (scoreAwareRetries m k eps slack boundSq)
    (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale) i x

theorem map_snd_slowActiveCostedSchedule
    (hn : 1 ≤ n) (m k : Nat) {q eps : Real} (hq : 0 < q)
    (K : Set (State n)) (hK : MeasurableSet K)
    (slack boundSq : Nat → Real) (scoreScale : Real) (i : Nat) (x : State n)
    [∀ j, IsProbabilityMeasure (slowExactTail m n q K j)] :
    Measure.map Prod.snd
        (slowActiveCostedSchedule hn m k q eps hq K hK slack boundSq scoreScale i x) =
      slowActiveSchedule hn m k q eps hq K hK slack boundSq scoreScale i x := by
  exact map_snd_costedActiveReferenceTailSchedule m
    (slowRawSchedule hn m k q eps hq K hK slack boundSq scoreScale)
    (slowRawCostedSchedule hn m k q eps hq K hK slack boundSq scoreScale)
    (slowExactTail m n q K)
    (map_snd_slowRawCostedSchedule hn m k hq K hK slack boundSq scoreScale) i x

/-- All retained phase-TV obligations for the slow schedule are closed. -/
theorem slowActive_phaseSeedTV
    (hn : 21 ≤ n) (m k : Nat) {q eps : Real} (hq4 : 4 ≤ q)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (slack boundSq : Nat → Real) (hslack : ∀ i, 0 < slack i)
    (hbound : ∀ i, 0 < boundSq i) (scoreScale : Real)
    (i : Nat) :
    TVLe
      ((slowRetainedSeedTarget m n q K i).bind (Kernel.map
        (slowActiveCostedSchedule (by omega : 1 ≤ n) m k q eps
          (lt_of_lt_of_le (by norm_num) hq4) K hK slack boundSq scoreScale i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
      (slowRetainedSeedTarget m n q K (i + 1))
      (slowPhaseError m k eps slack boundSq i) := by
  letI : ∀ j, IsProbabilityMeasure
      (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale j) := fun j ↦
    isProbabilityMeasure_slowRadiusQFallback (by omega : 1 ≤ n)
      (by unfold slowSourceInitialVariance; positivity) scoreScale j
  letI : ∀ j, IsProbabilityMeasure (slowRetainedSeedTarget m n q K j) := fun j ↦
    isProbabilityMeasure_slowRetainedSeedTarget (by omega : 1 ≤ n) hq4 hball j
  letI : ∀ j, IsProbabilityMeasure (slowExactTail m n q K j) := fun j ↦ by
    unfold slowExactTail
    exact Measure.isProbabilityMeasure_map
      ((by fun_prop : Measurable (fun y : State n ↦ ((0 : State n), y))).aemeasurable)
  by_cases hi : i + 1 < m
  · unfold slowActiveCostedSchedule slowPhaseError activeReferenceMixError
    simp only [costedActiveReferenceTailSchedule, if_pos hi]
    have hshare := scoreAwareShare_pos (m := m) (k := k) heps hslack hbound i
    have heta0 : scoreAwareEta m k eps slack boundSq i ≠ 0 := by
      unfold scoreAwareEta
      exact (ENNReal.ofReal_pos.mpr hshare).ne'
    have hetaTop : scoreAwareEta m k eps slack boundSq i ≠ ⊤ := ENNReal.ofReal_ne_top
    have heta1 : scoreAwareEta m k eps slack boundSq i ≤ 1 := by
      unfold scoreAwareEta
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal
        (scoreAwareShare_lt_one heps heps1 i).le
    have hzeta0 : scoreAwareZeta m k eps slack boundSq i ≠ 0 := by
      unfold scoreAwareZeta
      exact (ENNReal.ofReal_pos.mpr (div_pos hshare (by norm_num))).ne'
    have hzetaTop : scoreAwareZeta m k eps slack boundSq i ≠ ⊤ := ENNReal.ofReal_ne_top
    have hM1 : 1 ≤ slowReferenceWarm := by
      unfold slowReferenceWarm
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [Real.one_le_exp (show (0 : Real) ≤ 1 by norm_num)]
    have hwarm := isWarm_slowRetainedSeedTarget (m := m) (i := i) (by omega : 2 ≤ n)
      hq4 hK hKc hball (by omega)
    have h := tvLe_bind_radiusQWarmFallbackCostedKernelOfSigma_nextSeed
      (m := m) hn (lt_of_lt_of_le (by norm_num) hq4)
      (slowSourceSigmaSq n (slowSourceInitialVariance n))
      (slowSourceSigmaSq_pos (by omega : 1 ≤ n)
        (by unfold slowSourceInitialVariance; positivity))
      hK hKc hball
      (slowScoreAwareSteps n m k q eps slack boundSq)
      (scoreAwareRetries m k eps slack boundSq)
      (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale)
      i (by omega) (slowRetainedSeedTarget m n q K i)
      hM1 (by unfold slowReferenceWarm; exact ENNReal.ofReal_ne_top)
      heta0 hetaTop heta1 hzeta0 hzetaTop
      (scoreAwareZeta_le_sixteenth heps heps1 i)
      (one_le_slow_radius (by omega : 1 ≤ n) hq4 (by rfl) i)
      (by simpa only [slowReferenceWarm, slowRadiusQSeedTarget] using hwarm)
      (scoreAwareRetries m k eps slack boundSq i) rfl rfl
    simpa only [slowRawCostedSchedule, slowRetainedSeedTarget,
      slowRadiusQLocalGraphSeedTarget, scoreAwareMixError] using h
  · unfold slowActiveCostedSchedule slowPhaseError activeReferenceMixError
    simp only [costedActiveReferenceTailSchedule, if_neg hi]
    have heq :
        (slowRetainedSeedTarget m n q K i).bind (Kernel.map
          (Kernel.const (State n)
            (Measure.map (fun z : ScoreSeed n ↦ ((0 : ENNReal), z))
              (slowExactTail m n q K (i + 1))))
          (fun y : ENNReal × ScoreSeed n ↦ y.2.2)) =
        slowRetainedSeedTarget m n q K (i + 1) := by
      rw [Kernel.map_const _ (by fun_prop), Measure.const_comp,
        measure_univ, one_smul]
      unfold slowExactTail
      rw [Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      exact Measure.map_id
    rw [heq]
    exact TVLe.refl _

/-- All retained expected phase costs are bounded by the explicit `2e` retry envelope. -/
theorem slowActive_phaseCost
    (hn : 21 ≤ n) (m k : Nat) {q eps : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (slack boundSq : Nat → Real) (scoreScale : Real) (i : Nat) :
    (∫⁻ x, heterogeneousStepMean
      (slowActiveCostedSchedule (by omega : 1 ≤ n) m k q eps
        (lt_of_lt_of_le (by norm_num) hq4) K hK slack boundSq scoreScale i) x
      ∂(slowRetainedSeedTarget m n q K i)) ≤
      slowPhaseCostBound n m k q eps slack boundSq i := by
  letI : ∀ j, IsProbabilityMeasure
      (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale j) := fun j ↦
    isProbabilityMeasure_slowRadiusQFallback (by omega : 1 ≤ n)
      (by unfold slowSourceInitialVariance; positivity) scoreScale j
  letI : ∀ j, IsProbabilityMeasure (slowRetainedSeedTarget m n q K j) := fun j ↦
    isProbabilityMeasure_slowRetainedSeedTarget (by omega : 1 ≤ n) hq4 hball j
  letI : ∀ j, IsProbabilityMeasure (slowExactTail m n q K j) := fun j ↦ by
    unfold slowExactTail
    exact Measure.isProbabilityMeasure_map
      ((by fun_prop : Measurable (fun y : State n ↦ ((0 : State n), y))).aemeasurable)
  by_cases hi : i + 1 < m
  · unfold slowActiveCostedSchedule slowPhaseCostBound
    simp only [costedActiveReferenceTailSchedule, if_pos hi]
    have hwarm := isWarm_slowRetainedSeedTarget (m := m) (i := i) (by omega : 2 ≤ n)
      hq4 hK hKc hball (by omega)
    have h := radiusQCostedOfSigma_referenceCost_le_of_warm
      (by omega : 2 ≤ n) (lt_of_lt_of_le (by norm_num) hq4)
      (slowSourceSigmaSq n (slowSourceInitialVariance n))
      (slowSourceSigmaSq_pos (by omega : 1 ≤ n)
        (by unfold slowSourceInitialVariance; positivity))
      hK hKc hball
      (slowScoreAwareSteps n m k q eps slack boundSq)
      (scoreAwareRetries m k eps slack boundSq)
      (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale)
      (slowRetainedSeedTarget m n q K i)
      (M := slowReferenceWarm)
      (by unfold slowReferenceWarm; exact ENNReal.ofReal_ne_top) i
      (one_le_slow_radius (by omega : 1 ≤ n) hq4 (by rfl) i)
      (by simpa only [slowReferenceWarm, slowRadiusQSeedTarget] using hwarm)
    simpa only [slowRawCostedSchedule, slowReferenceWarm,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.exp 1)] using h
  · unfold slowActiveCostedSchedule slowPhaseCostBound
    simp only [costedActiveReferenceTailSchedule, if_neg hi, Kernel.const_apply]
    change (∫⁻ _x, ∫⁻ y, y.1
      ∂Measure.map (fun z : ScoreSeed n ↦ ((0 : ENNReal), z))
        (slowExactTail m n q K (i + 1))
      ∂slowRetainedSeedTarget m n q K i) ≤ 0
    have hinner : (∫⁻ y, y.1
        ∂Measure.map (fun z : ScoreSeed n ↦ ((0 : ENNReal), z))
          (slowExactTail m n q K (i + 1))) = 0 := by
      rw [lintegral_map]
      · simp
      · fun_prop
      · fun_prop
    simp only [hinner]
    simp

noncomputable def slowOperationalPhases (n : Nat) (N : Real) : Nat :=
  slowSourcePhases n N (slowSourceInitialVariance n)

theorem slowPhaseError_sum_le_one_fortieth
    {m k : Nat} {eps : Real} (heps : 0 < eps) (heps1 : eps ≤ 1)
    {slack boundSq : Nat → Real}
    (hslack : ∀ i, 0 < slack i) (hbound : ∀ i, 0 < boundSq i) :
    (k : ENNReal) * (∑ i ∈ range m,
      slowPhaseError m k eps slack boundSq i) ≤
        ENNReal.ofReal (1 / 40 : Real) := by
  have hmono : (∑ i ∈ range m, slowPhaseError m k eps slack boundSq i) ≤
      ∑ i ∈ range m, scoreAwareMixError m k eps slack boundSq i := by
    apply sum_le_sum
    intro i hi
    unfold slowPhaseError activeReferenceMixError
    split
    · exact le_rfl
    · exact bot_le
  calc
    (k : ENNReal) * (∑ i ∈ range m,
        slowPhaseError m k eps slack boundSq i) ≤
      (k : ENNReal) * (∑ i ∈ range m,
        scoreAwareMixError m k eps slack boundSq i) := mul_le_mul_left' hmono _
    _ ≤ ENNReal.ofReal (1 / 80 : Real) :=
      scoreAwareMixError_sum_le_one_eightieth heps heps1 hslack hbound
    _ ≤ ENNReal.ofReal (1 / 40 : Real) := ENNReal.ofReal_le_ofReal (by norm_num)

/-- Strongest closed phase-analytic capstone for the honest slow schedule.

There is no phase-TV, phase-cost, warmness, kernel, erasure, or audit argument.  The
remaining three hypotheses are respectively pure aggregate dependence accounting,
pure aggregate query accounting, and the ordinary weighted-readout accuracy theorem. -/
theorem exists_sourceReferenceTVOneRunCertificate_slowSource
    (hn : 21 ≤ n) (k : Nat) {N q eps : Real} (hN : 0 < N) (hq4 : 4 ≤ q)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (slack boundSq : Nat → Real) (hslack : ∀ i, 0 < slack i)
    (hbound : ∀ i, 0 < boundSq i) (scoreScale : Real)
    (readout :
      (Fin k → ((Finset.Iic (slowOperationalPhases n N) → State n) × State n)) → Real)
    (hreadout : Measurable readout)
    {runtimeConstant R requested lo hi : Real}
    (hbudget : (k : ENNReal) *
        (∑ i ∈ range (slowOperationalPhases n N),
          slowPhaseCostBound n (slowOperationalPhases n N) k q eps slack boundSq i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R requested)
    (haccuracy : 4 / 5 ≤
      (@Ttc.CVIndependentStreamDependence.independentPathLaw _ _ k
        (stateScheduleFromSeed
          (slowActiveSchedule (by omega : 1 ≤ n) (slowOperationalPhases n N) k q eps
            (lt_of_lt_of_le (by norm_num) hq4) K hK slack boundSq scoreScale))
        (by
          letI : ∀ j, IsProbabilityMeasure
              (slowRetainedSeedTarget (slowOperationalPhases n N) n q K j) := fun j ↦
            isProbabilityMeasure_slowRetainedSeedTarget (by omega : 1 ≤ n) hq4 hball j
          letI : ∀ j, IsProbabilityMeasure
              (slowExactTail (slowOperationalPhases n N) n q K j) := fun j ↦ by
            unfold slowExactTail
            exact Measure.isProbabilityMeasure_map
              ((by fun_prop : Measurable
                (fun y : State n ↦ ((0 : State n), y))).aemeasurable)
          intro i
          infer_instance)
        (slowInitialPair n)).real
        {omega | readout
          (independentPathScorePrefixCurrent (slowOperationalPhases n N) omega) ∈
            Icc lo hi}) :
    ∃ reference : Measure
        (Fin k → HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (@independentHeterogeneousRetainedPathLaw _ _ _ _ k
          (slowActiveCostedSchedule (by omega : 1 ≤ n)
            (slowOperationalPhases n N) k q eps
            (lt_of_lt_of_le (by norm_num) hq4) K hK slack boundSq scoreScale)
          (by
            letI : ∀ j, IsProbabilityMeasure
                (slowRetainedSeedTarget (slowOperationalPhases n N) n q K j) := fun j ↦
              isProbabilityMeasure_slowRetainedSeedTarget (by omega : 1 ≤ n) hq4 hball j
            letI : ∀ j, IsProbabilityMeasure
                (slowExactTail (slowOperationalPhases n N) n q K j) := fun j ↦ by
              unfold slowExactTail
              exact Measure.isProbabilityMeasure_map
                ((by fun_prop : Measurable
                  (fun y : State n ↦ ((0 : State n), y))).aemeasurable)
            intro i
            infer_instance)
          (slowInitialPair n) (slowOperationalPhases n N))
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ readout
          (independentStoredScorePrefixCurrent (slowOperationalPhases n N) omega))
        runtimeConstant n R requested lo hi := by
  let m := slowOperationalPhases n N
  have hn1 : 1 ≤ n := by omega
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq4
  letI : ∀ j, IsProbabilityMeasure
      (slowRadiusQFallback n (slowSourceInitialVariance n) scoreScale j) := fun j ↦
    isProbabilityMeasure_slowRadiusQFallback hn1
      (by unfold slowSourceInitialVariance; positivity) scoreScale j
  letI : ∀ j, IsProbabilityMeasure (slowRetainedSeedTarget m n q K j) := fun j ↦
    isProbabilityMeasure_slowRetainedSeedTarget hn1 hq4 hball j
  letI : IsProbabilityMeasure (slowInitialPair n) := by
    unfold slowInitialPair
    letI : IsProbabilityMeasure (slowInitialSeed n) :=
      isProbabilityMeasure_slowInitialSeed hn1
    exact Measure.isProbabilityMeasure_map
      ((by fun_prop : Measurable (fun y : State n ↦ ((0 : State n), y))).aemeasurable)
  letI : ∀ j, IsProbabilityMeasure (slowExactTail m n q K j) := fun j ↦ by
    unfold slowExactTail
    exact Measure.isProbabilityMeasure_map
      ((by fun_prop : Measurable (fun y : State n ↦ ((0 : State n), y))).aemeasurable)
  letI : ∀ j, IsMarkovKernel
      (slowRawSchedule hn1 m k q eps hq0 K hK slack boundSq scoreScale j) := fun j ↦ by
    unfold slowRawSchedule
    infer_instance
  letI : ∀ j, IsMarkovKernel
      (slowRawCostedSchedule hn1 m k q eps hq0 K hK slack boundSq scoreScale j) :=
    fun j ↦ by
      unfold slowRawCostedSchedule
      infer_instance
  letI : ∀ j, IsMarkovKernel
      (slowActiveSchedule hn1 m k q eps hq0 K hK slack boundSq scoreScale j) := fun j ↦ by
    unfold slowActiveSchedule
    infer_instance
  letI : ∀ j, IsMarkovKernel
      (slowActiveCostedSchedule hn1 m k q eps hq0 K hK slack boundSq scoreScale j) :=
    fun j ↦ by
      unfold slowActiveCostedSchedule
      infer_instance
  apply exists_sourceReferenceTVOneRunCertificate_of_pathReadoutAccuracy
    (slowActiveCostedSchedule hn1 m k q eps hq0 K hK slack boundSq scoreScale)
    (slowActiveSchedule hn1 m k q eps hq0 K hK slack boundSq scoreScale)
    (slowInitialPair n)
    (fun i x ↦ map_snd_slowActiveCostedSchedule hn1 m k (eps := eps) hq0 K hK
      slack boundSq scoreScale i x)
    (initialHeterogeneousHistoryLaw (slowInitialPair n))
    (slowRetainedSeedTarget m n q K)
    (slowPhaseError m k eps slack boundSq)
    (slowPhaseCostBound n m k q eps slack boundSq)
    (d := 0) (initialBudget := 0)
    (TVLe.refl _)
  · unfold initialHeterogeneousHistoryLaw
    rw [Measure.map_map measurable_snd measurable_initialHeterogeneousHistoryState]
    exact map_snd_slowInitialPair n
  · unfold initialHeterogeneousHistoryLaw
    change (∫⁻ z, (Prod.fst ∘ Prod.fst) z
      ∂Measure.map initialHeterogeneousHistoryState (slowInitialPair n)) ≤ 0
    rw [lintegral_map (measurable_fst.comp measurable_fst)
      measurable_initialHeterogeneousHistoryState]
    simp [initialHeterogeneousHistoryState]
  · exact slowActive_phaseSeedTV hn m k hq4 heps heps1 hK hKc hball
      slack boundSq hslack hbound scoreScale
  · exact slowActive_phaseCost hn m k hq4 hK hKc hball
      slack boundSq scoreScale
  · exact hreadout
  · simpa only [m, zero_add] using
      (slowPhaseError_sum_le_one_fortieth heps heps1 hslack hbound)
  · simpa only [m, zero_add] using hbudget
  · simpa only [m] using haccuracy

#print axioms slowActive_phaseSeedTV
#print axioms slowActive_phaseCost
#print axioms exists_sourceReferenceTVOneRunCertificate_slowSource

end Ttc.CVSlowSourceReferenceCertificate
