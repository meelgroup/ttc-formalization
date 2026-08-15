import Ttc.Exec.CVSlowSourceReferenceCertificate
import Ttc.Exec.CVSlowRadiusQCanonicalOperational
import Ttc.Exec.CVSlowRadiusQReferenceCost
import Ttc.Exec.CVGaussianCappedCostedSchedule

/-! Retained phase TV and cost for the recursive-deadline slow kernel. -/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Ttc.CVSlowCanonicalRetainedReference

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowRadiusQFallbackSchedule
open Ttc.CVSlowRadiusQReferencePhaseTV Ttc.CVSlowRadiusQReferenceCost
open Ttc.CVSlowSourceReferenceCertificate Ttc.CVSlowRadiusQRecursiveOperational
open Ttc.CVSlowRadiusQCanonicalOperational Ttc.CVGaussianScoreAwareParameters
open Ttc.CVWarmBudgetRecurrence Ttc.CVIndependentRefreshSeedLaws
open Ttc.CVHeterogeneousHistoryReference
open Ttc.CVGaussianCappedCostedSchedule
open Ttc.CVConcreteAugmentedRetryCutoffBudget
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def slowStationaryTail
    (n : Nat) (q s0 : Real) (K : Set (State n)) (i : Nat) : Measure (ScoreSeed n) :=
  Measure.map (fun y : State n ↦ ((0 : State n), y))
    (slowRadiusQSeedTarget n q s0 K i)

theorem map_snd_slowStationaryTail
    (n : Nat) (q s0 : Real) (K : Set (State n)) (i : Nat) :
    Measure.map Prod.snd (slowStationaryTail n q s0 K i) =
      slowRadiusQSeedTarget n q s0 K i := by
  unfold slowStationaryTail
  rw [Measure.map_map measurable_snd (by fun_prop)]
  exact Measure.map_id

theorem isProbabilityMeasure_slowStationaryTail
    (hn : 1 ≤ n) {q s0 : Real} (hq : 0 < q) (hs0 : 0 < s0)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (hrad : ∀ i, 1 ≤ q * Real.sqrt (slowSourceSigmaSq n s0 i) * Real.sqrt n)
    (i : Nat) : IsProbabilityMeasure (slowStationaryTail n q s0 K i) := by
  unfold slowStationaryTail
  letI : IsProbabilityMeasure (slowRadiusQSeedTarget n q s0 K i) :=
    isProbabilityMeasure_slowRadiusQSeedTarget hn hq hs0 hK hKc hball i (hrad i)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

noncomputable def slowCanonicalCostedActiveSchedule
    (hn : 1 ≤ n) (cutoff k : Nat) {q s0 eps : Real} (hq : 0 < q) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K) (scoreScale : Real)
    (initialWarm : ENNReal) (slack boundSq : Nat → Real) :
    Nat → Kernel (State n) (ENNReal × ScoreSeed n) :=
  costedActiveReferenceTailSchedule cutoff
    (slowWarmFallbackCostedSchedule hn q hq hs0 K hK
      (slowCanonicalSteps initialWarm n q s0 K
        (scoreAwareRetries cutoff k eps slack boundSq)
        (scoreAwareEta cutoff k eps slack boundSq)
        (scoreAwareZeta cutoff k eps slack boundSq))
      (scoreAwareRetries cutoff k eps slack boundSq) scoreScale)
    (slowStationaryTail n q s0 K)

noncomputable def slowCanonicalActiveSchedule
    (hn : 1 ≤ n) (cutoff k : Nat) {q s0 eps : Real} (hq : 0 < q) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K) (scoreScale : Real)
    (initialWarm : ENNReal) (slack boundSq : Nat → Real) :
    Nat → Kernel (State n) (ScoreSeed n) :=
  activeReferenceTailSchedule cutoff
    (slowWarmFallbackSchedule hn q hq hs0 K hK
      (slowCanonicalSteps initialWarm n q s0 K
        (scoreAwareRetries cutoff k eps slack boundSq)
        (scoreAwareEta cutoff k eps slack boundSq)
        (scoreAwareZeta cutoff k eps slack boundSq))
      (scoreAwareRetries cutoff k eps slack boundSq) scoreScale)
    (slowStationaryTail n q s0 K)

instance slowCanonicalActiveSchedule.isMarkovKernel
    (hn : 1 ≤ n) (cutoff k : Nat) {q s0 eps : Real} (hq : 0 < q) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K) (scoreScale : Real)
    (initialWarm : ENNReal) (slack boundSq : Nat → Real)
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q s0 K j)] (i : Nat) :
    IsMarkovKernel (slowCanonicalActiveSchedule hn cutoff k (eps := eps) hq hs0 K hK scoreScale
      initialWarm slack boundSq i) := by
  unfold slowCanonicalActiveSchedule
  infer_instance

instance slowCanonicalCostedActiveSchedule.isMarkovKernel
    (hn : 1 ≤ n) (cutoff k : Nat) {q s0 eps : Real} (hq : 0 < q) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K) (scoreScale : Real)
    (initialWarm : ENNReal) (slack boundSq : Nat → Real)
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q s0 K j)] (i : Nat) :
    IsMarkovKernel (slowCanonicalCostedActiveSchedule hn cutoff k (eps := eps) hq hs0 K hK scoreScale
      initialWarm slack boundSq i) := by
  unfold slowCanonicalCostedActiveSchedule
  infer_instance

theorem map_snd_slowCanonicalCostedActiveSchedule
    (hn : 1 ≤ n) (cutoff k : Nat) {q s0 eps : Real} (hq : 0 < q) (hs0 : 0 < s0)
    (K : Set (State n)) (hK : MeasurableSet K) (scoreScale : Real)
    (initialWarm : ENNReal) (slack boundSq : Nat → Real)
    [∀ j, IsProbabilityMeasure (slowStationaryTail n q s0 K j)]
    (i : Nat) (x : State n) :
    Measure.map Prod.snd
      (slowCanonicalCostedActiveSchedule hn cutoff k (eps := eps) hq hs0 K hK scoreScale
        initialWarm slack boundSq i x) =
      slowCanonicalActiveSchedule hn cutoff k (eps := eps) hq hs0 K hK scoreScale
        initialWarm slack boundSq i x := by
  exact map_snd_costedActiveReferenceTailSchedule cutoff
    (slowWarmFallbackSchedule hn q hq hs0 K hK
      (slowCanonicalSteps initialWarm n q s0 K
        (scoreAwareRetries cutoff k eps slack boundSq)
        (scoreAwareEta cutoff k eps slack boundSq)
        (scoreAwareZeta cutoff k eps slack boundSq))
      (scoreAwareRetries cutoff k eps slack boundSq) scoreScale)
    (slowWarmFallbackCostedSchedule hn q hq hs0 K hK
      (slowCanonicalSteps initialWarm n q s0 K
        (scoreAwareRetries cutoff k eps slack boundSq)
        (scoreAwareEta cutoff k eps slack boundSq)
        (scoreAwareZeta cutoff k eps slack boundSq))
      (scoreAwareRetries cutoff k eps slack boundSq) scoreScale)
    (slowStationaryTail n q s0 K)
    (map_snd_slowWarmFallbackCostedSchedule hn q hq hs0 K hK
      (slowCanonicalSteps initialWarm n q s0 K
        (scoreAwareRetries cutoff k eps slack boundSq)
        (scoreAwareEta cutoff k eps slack boundSq)
        (scoreAwareZeta cutoff k eps slack boundSq))
      (scoreAwareRetries cutoff k eps slack boundSq) scoreScale) i x

theorem initial_le_recursiveWarmBudget
    {initial : ENNReal} {accepted fallback : Nat → ENNReal}
    (haccepted : ∀ i, 1 ≤ accepted i) :
    ∀ i, initial ≤ recursiveWarmBudget initial accepted fallback i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      rw [recursiveWarmBudget_succ]
      exact ih.trans ((le_mul_of_one_le_left' (haccepted i)).trans
        (le_add_of_nonneg_right bot_le))

/-- Every retained phase has the local score/seed error selected by the score-aware
share, even though the common executable deadline uses the larger recursive warmth. -/
theorem slowCanonical_retained_phaseSeedTV
    (hn : 21 ≤ n) (m k : Nat) (hk : 1 ≤ k)
    {q eps : Real} (hq4 : 4 ≤ q) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (slack boundSq : Nat → Real) (hslack : ∀ i, 0 < slack i)
    (hbound : ∀ i, 0 < boundSq i) (scoreScale : Real)
    {i : Nat} (hi : i < m) :
    TVLe
      ((slowRetainedSeedTarget m n q K i).bind (Kernel.map
        (slowCanonicalCostedActiveSchedule (by omega : 1 ≤ n) (m + 1) k
          (q := q) (eps := eps)
          (lt_of_lt_of_le (by norm_num) hq4)
          (s0 := slowSourceInitialVariance n)
          (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
          slowReferenceWarm slack boundSq i)
        (fun y : ENNReal × ScoreSeed n ↦ y.2.2)))
      (slowRetainedSeedTarget m n q K (i + 1))
      (scoreAwareMixError (m + 1) k eps slack boundSq i) := by
  let hn1 : 1 ≤ n := by omega
  let s0 := slowSourceInitialVariance n
  let retries := scoreAwareRetries (m + 1) k eps slack boundSq
  let etaShare := scoreAwareEta (m + 1) k eps slack boundSq
  let zetaShare := scoreAwareZeta (m + 1) k eps slack boundSq
  let steps := slowCanonicalSteps slowReferenceWarm n q s0 K retries etaShare zetaShare
  let warm := slowWarmBudget slowReferenceWarm n q s0 K retries
  letI : ∀ j, IsProbabilityMeasure (slowRadiusQFallback n s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_slowRadiusQFallback hn1
      (by unfold s0 slowSourceInitialVariance; positivity) scoreScale j
  letI : ∀ j, IsProbabilityMeasure (slowRetainedSeedTarget m n q K j) := fun j ↦
    isProbabilityMeasure_slowRetainedSeedTarget hn1 hq4 hball j
  letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n q s0 K j) := fun j ↦
    isProbabilityMeasure_slowStationaryTail hn1 (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold s0 slowSourceInitialVariance; positivity) hK hKc hball
      (fun r ↦ one_le_slow_radius hn1 hq4 (by rfl) r) j
  unfold slowCanonicalCostedActiveSchedule
  simp only [costedActiveReferenceTailSchedule, if_pos (by omega : i + 1 < m + 1)]
  have hwarm0 := isWarm_slowRetainedSeedTarget (m := m) (i := i)
    (by omega : 2 ≤ n) hq4 hK hKc hball hi
  have hwarmLower : slowReferenceWarm ≤ 2 * warm i :=
    (initial_le_recursiveWarmBudget (one_le_slowAcceptedFactor retries) i).trans
      (le_mul_of_one_le_left' (by norm_num))
  have hwarm : IsWarm (2 * warm i) (slowRetainedSeedTarget m n q K i)
      (slowRadiusQSeedTarget n q s0 K i) := by
    exact hwarm0.mono hwarmLower
  have hWarmOne : 1 ≤ slowReferenceWarm := by
    unfold slowReferenceWarm
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [Real.one_le_exp (show (0 : Real) ≤ 1 by norm_num)]
  have hrecOne : 1 ≤ warm i := one_le_recursiveWarmBudget hWarmOne
    (one_le_slowAcceptedFactor retries) i
  have hrecTop : warm i ≠ ⊤ := recursiveWarmBudget_ne_top
    (by unfold slowReferenceWarm; exact ENNReal.ofReal_ne_top)
    (fun j ↦ by unfold slowAcceptedFactor; finiteness)
    (slowFallbackFactor_ne_top hn1
      (by unfold s0 slowSourceInitialVariance; positivity) hK) i
  have h := tvLe_bind_radiusQWarmFallbackCostedKernelOfSigma_nextSeed
    (m := m) (M := 2 * warm i) (eta := etaShare i) (zeta := zetaShare i)
    hn (lt_of_lt_of_le (by norm_num) hq4)
    (slowSourceSigmaSq n s0) (slowSourceSigmaSq_pos hn1
      (by unfold s0 slowSourceInitialVariance; positivity)) hK hKc hball
    steps retries (slowRadiusQFallback n s0 scoreScale) i hi
    (slowRetainedSeedTarget m n q K i)
    (hrecOne.trans (le_mul_of_one_le_left' (by norm_num)))
    (ENNReal.mul_ne_top (by simp) hrecTop)
    (ENNReal.ofReal_ne_zero_iff.mpr
      (scoreAwareShare_pos (m := m + 1) (k := k) heps hslack hbound i))
    ENNReal.ofReal_ne_top
    (by
      change ENNReal.ofReal (scoreAwareShare (m + 1) k eps slack boundSq i) ≤ 1
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal
        (scoreAwareShare_lt_one (m := m + 1) (k := k) heps heps1 i).le)
    (ENNReal.ofReal_ne_zero_iff.mpr
      (div_pos (scoreAwareShare_pos (m := m + 1) (k := k)
        heps hslack hbound i) (by norm_num)))
    ENNReal.ofReal_ne_top
    (scoreAwareZeta_le_sixteenth (m := m + 1) (k := k) heps heps1 i)
    (one_le_slow_radius hn1 hq4 (by rfl) i) hwarm (retries i) (by rfl) rfl
  simpa only [slowWarmFallbackCostedSchedule, steps, retries, etaShare, zetaShare,
    warm, slowWarmBudget, s0, slowReferenceWarm, scoreAwareMixError,
    slowRetainedSeedTarget, slowRadiusQLocalGraphSeedTarget] using h

noncomputable def slowCanonicalPhaseCostBound
    (n cutoff k : Nat) (q s0 eps : Real) (K : Set (State n))
    (initialWarm : ENNReal) (slack boundSq : Nat → Real) (i : Nat) : ENNReal :=
  ENNReal.ofReal (retryReferenceMeanEnvelope (2 * Real.exp 1)
    (slowCanonicalSteps initialWarm n q s0 K
      (scoreAwareRetries cutoff k eps slack boundSq)
      (scoreAwareEta cutoff k eps slack boundSq)
      (scoreAwareZeta cutoff k eps slack boundSq) i)
    (scoreAwareRetries cutoff k eps slack boundSq i))

/-- Expected retained cost has the constant `2e` multiplier.  Recursive actual warmth
appears only inside `slowCanonicalSteps`, hence only logarithmically in the deadline. -/
theorem slowCanonical_retained_phaseCost
    (hn : 21 ≤ n) (m k : Nat) {q eps : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K)
    (slack boundSq : Nat → Real) (scoreScale : Real)
    {i : Nat} (hi : i < m) :
    (∫⁻ x, heterogeneousStepMean
      (slowCanonicalCostedActiveSchedule (by omega : 1 ≤ n) (m + 1) k
        (q := q) (eps := eps) (s0 := slowSourceInitialVariance n)
        (lt_of_lt_of_le (by norm_num) hq4)
        (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
        slowReferenceWarm slack boundSq i) x
      ∂(slowRetainedSeedTarget m n q K i)) ≤
      slowCanonicalPhaseCostBound n (m + 1) k q (slowSourceInitialVariance n)
        eps K slowReferenceWarm slack boundSq i := by
  let hn1 : 1 ≤ n := by omega
  let s0 := slowSourceInitialVariance n
  let retries := scoreAwareRetries (m + 1) k eps slack boundSq
  let etaShare := scoreAwareEta (m + 1) k eps slack boundSq
  let zetaShare := scoreAwareZeta (m + 1) k eps slack boundSq
  let steps := slowCanonicalSteps slowReferenceWarm n q s0 K retries etaShare zetaShare
  letI : ∀ j, IsProbabilityMeasure (slowRadiusQFallback n s0 scoreScale j) :=
    fun j ↦ isProbabilityMeasure_slowRadiusQFallback hn1
      (by unfold s0 slowSourceInitialVariance; positivity) scoreScale j
  letI : ∀ j, IsProbabilityMeasure (slowRetainedSeedTarget m n q K j) := fun j ↦
    isProbabilityMeasure_slowRetainedSeedTarget hn1 hq4 hball j
  letI : ∀ j, IsProbabilityMeasure (slowStationaryTail n q s0 K j) := fun j ↦
    isProbabilityMeasure_slowStationaryTail hn1 (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold s0 slowSourceInitialVariance; positivity) hK hKc hball
      (fun r ↦ one_le_slow_radius hn1 hq4 (by rfl) r) j
  unfold slowCanonicalCostedActiveSchedule
  simp only [costedActiveReferenceTailSchedule, if_pos (by omega : i + 1 < m + 1)]
  have hwarm := isWarm_slowRetainedSeedTarget (m := m) (i := i)
    (by omega : 2 ≤ n) hq4 hK hKc hball hi
  have h := radiusQCostedOfSigma_referenceCost_le_of_warm
    (by omega : 2 ≤ n) (lt_of_lt_of_le (by norm_num) hq4)
    (slowSourceSigmaSq n s0)
    (slowSourceSigmaSq_pos hn1 (by unfold s0 slowSourceInitialVariance; positivity))
    hK hKc hball steps retries (slowRadiusQFallback n s0 scoreScale)
    (slowRetainedSeedTarget m n q K i) (M := slowReferenceWarm)
    (by unfold slowReferenceWarm; exact ENNReal.ofReal_ne_top) i
    (one_le_slow_radius hn1 hq4 (by rfl) i)
    (by simpa only [slowReferenceWarm, slowRadiusQSeedTarget, s0] using hwarm)
  simpa only [slowWarmFallbackCostedSchedule, slowCanonicalPhaseCostBound,
    steps, retries, etaShare, zetaShare, s0, slowReferenceWarm,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.exp 1)] using h

#print axioms slowCanonical_retained_phaseSeedTV
#print axioms slowCanonical_retained_phaseCost
#print axioms map_snd_slowCanonicalCostedActiveSchedule

end Ttc.CVSlowCanonicalRetainedReference
