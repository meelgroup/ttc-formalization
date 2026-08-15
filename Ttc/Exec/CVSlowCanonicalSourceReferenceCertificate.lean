import Ttc.Exec.CVSlowCanonicalRetainedReference
import Ttc.Exec.CVRelativeWeightedRetainedCertificate

/-! Retained reference certificate for the recursive-deadline slow sampler. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Ttc.CVSlowCanonicalSourceReferenceCertificate

open MeasureTheory ProbabilityTheory Metric Set Finset
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVSequentialPhaseSampler Ttc.CVScoreSeedPhaseKernel
open Ttc.CVSlowSourceReferenceCertificate Ttc.CVSlowCanonicalRetainedReference
open Ttc.CVSlowRadiusQReferencePhaseTV Ttc.CVSlowFullBodySourceSchedule
open Ttc.CVGaussianWarmFallbackCappedOperational Ttc.CVGaussianScoreAwareParameters
open Ttc.CVHeterogeneousHistoryReference Ttc.CVHeterogeneousRetainedPathLaw
open Ttc.CVRelativeWeightedRetainedCertificate Ttc.CVSourceReferenceTVCapstone
open Ttc.CVIndependentStreamDependence
open Ttc.CVGaussianCappedCostedSchedule
open scoped ENNReal Classical BigOperators

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)
abbrev ScoreSeed (n : Nat) := State n × State n

noncomputable def slowCanonicalRetainedSeedTarget
    (m n : Nat) (q : Real) (K : Set (State n)) (i : Nat) : Measure (State n) :=
  if i ≤ m then slowRetainedSeedTarget m n q K i
  else slowRadiusQSeedTarget n q (slowSourceInitialVariance n) K i

noncomputable def slowCanonicalRetainedError
    (m k : Nat) (eps : Real) (slack boundSq : Nat → Real) (i : Nat) : ENNReal :=
  if i < m then scoreAwareMixError (m + 1) k eps slack boundSq i else 0

noncomputable def slowCanonicalRetainedCost
    (n m k : Nat) (q eps : Real) (K : Set (State n))
    (slack boundSq : Nat → Real) (i : Nat) : ENNReal :=
  if i < m then slowCanonicalPhaseCostBound n (m + 1) k q
    (slowSourceInitialVariance n) eps K slowReferenceWarm slack boundSq i else 0

theorem isProbabilityMeasure_slowCanonicalRetainedSeedTarget
    (hn : 1 ≤ n) (m : Nat) {q : Real} (hq4 : 4 ≤ q)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (i : Nat) :
    IsProbabilityMeasure (slowCanonicalRetainedSeedTarget m n q K i) := by
  unfold slowCanonicalRetainedSeedTarget
  split
  · exact isProbabilityMeasure_slowRetainedSeedTarget hn hq4 hball i
  · exact isProbabilityMeasure_slowRadiusQSeedTarget hn
      (lt_of_lt_of_le (by norm_num) hq4)
      (by unfold slowSourceInitialVariance; positivity) hK hKc hball i
      (one_le_slow_radius hn hq4 (by rfl) i)

/-- All sampler/retained-reference obligations are closed.  Only aggregate dependence,
aggregate runtime, and the estimator accuracy statement are visible. -/
theorem exists_sourceReferenceTVOneRunCertificate_slowCanonical
    (hn : 21 ≤ n) (m k : Nat) (hk : 1 ≤ k)
    {q eps : Real} (hq4 : 4 ≤ q) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (slack boundSq : Nat → Real) (hslack : ∀ i, 0 < slack i)
    (hbound : ∀ i, 0 < boundSq i) (scoreScale : Real)
    (readout : (Fin k → ((Finset.Iic m → State n) × State n)) → Real)
    (hreadout : Measurable readout)
    {runtimeConstant R requested lo hi : Real}
    (herror : (k : ENNReal) * (∑ i ∈ range m,
      slowCanonicalRetainedError m k eps slack boundSq i) ≤ ENNReal.ofReal (1 / 40 : Real))
    (hbudget : (k : ENNReal) * (∑ i ∈ range m,
      slowCanonicalRetainedCost n m k q eps K slack boundSq i) ≤
      Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryBudget
        runtimeConstant n R requested)
    (haccuracy : 4 / 5 ≤
      (@independentPathLaw _ _ k
        (stateScheduleFromSeed
          (slowCanonicalActiveSchedule (by omega : 1 ≤ n) (m + 1) k
            (q := q) (eps := eps) (s0 := slowSourceInitialVariance n)
            (lt_of_lt_of_le (by norm_num) hq4)
            (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
            slowReferenceWarm slack boundSq))
        (by
          letI : ∀ j, IsProbabilityMeasure
              (slowStationaryTail n q (slowSourceInitialVariance n) K j) := fun j ↦
            isProbabilityMeasure_slowStationaryTail (by omega : 1 ≤ n)
              (lt_of_lt_of_le (by norm_num) hq4)
              (by unfold slowSourceInitialVariance; positivity) hK hKc hball
              (fun r ↦ one_le_slow_radius (by omega : 1 ≤ n) hq4 (by rfl) r) j
          intro i; infer_instance)
        (slowInitialPair n)).real
        {omega | readout (independentPathScorePrefixCurrent m omega) ∈ Icc lo hi}) :
    ∃ reference : Measure (Fin k → HeterogeneousHistoryState (State n) (State n)),
      SourceReferenceTVOneRunCertificate
        (@independentHeterogeneousRetainedPathLaw _ _ _ _ k
          (slowCanonicalCostedActiveSchedule (by omega : 1 ≤ n) (m + 1) k
            (q := q) (eps := eps) (s0 := slowSourceInitialVariance n)
            (lt_of_lt_of_le (by norm_num) hq4)
            (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
            slowReferenceWarm slack boundSq)
          (by
            letI : ∀ j, IsProbabilityMeasure
                (slowStationaryTail n q (slowSourceInitialVariance n) K j) := fun j ↦
              isProbabilityMeasure_slowStationaryTail (by omega : 1 ≤ n)
                (lt_of_lt_of_le (by norm_num) hq4)
                (by unfold slowSourceInitialVariance; positivity) hK hKc hball
                (fun r ↦ one_le_slow_radius (by omega : 1 ≤ n) hq4 (by rfl) r) j
            intro i; infer_instance)
          (slowInitialPair n) m)
        reference (fun omega ↦ ∑ j, (omega j).1.1)
        (fun omega ↦ readout (independentStoredScorePrefixCurrent m omega))
        runtimeConstant n R requested lo hi := by
  let hn1 : 1 ≤ n := by omega
  let hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq4
  letI : ∀ j, IsProbabilityMeasure
      (slowStationaryTail n q (slowSourceInitialVariance n) K j) := fun j ↦
    isProbabilityMeasure_slowStationaryTail hn1 hq0
      (by unfold slowSourceInitialVariance; positivity) hK hKc hball
      (fun r ↦ one_le_slow_radius hn1 hq4 (by rfl) r) j
  letI : ∀ j, IsProbabilityMeasure
      (slowCanonicalRetainedSeedTarget m n q K j) := fun j ↦
    isProbabilityMeasure_slowCanonicalRetainedSeedTarget hn1 m hq4 hK hKc hball j
  letI : IsProbabilityMeasure (slowInitialPair n) := by
    unfold slowInitialPair
    letI : IsProbabilityMeasure (slowInitialSeed n) := isProbabilityMeasure_slowInitialSeed hn1
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  apply exists_sourceReferenceTVOneRunCertificate_of_pathReadoutAccuracy
    (slowCanonicalCostedActiveSchedule hn1 (m + 1) k hq0
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    (slowCanonicalActiveSchedule hn1 (m + 1) k hq0
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq)
    (slowInitialPair n)
    (fun i x ↦ map_snd_slowCanonicalCostedActiveSchedule hn1 (m + 1) k hq0
      (by unfold slowSourceInitialVariance; positivity) K hK scoreScale
      slowReferenceWarm slack boundSq i x)
    (initialHeterogeneousHistoryLaw (slowInitialPair n))
    (slowCanonicalRetainedSeedTarget m n q K)
    (slowCanonicalRetainedError m k eps slack boundSq)
    (slowCanonicalRetainedCost n m k q eps K slack boundSq)
    (d := 0) (initialBudget := 0) (TVLe.refl _)
  · unfold initialHeterogeneousHistoryLaw
    rw [Measure.map_map measurable_snd measurable_initialHeterogeneousHistoryState]
    change Measure.map Prod.snd (slowInitialPair n) = slowInitialSeed n
    exact map_snd_slowInitialPair n
  · unfold initialHeterogeneousHistoryLaw
    change (∫⁻ z, (Prod.fst ∘ Prod.fst) z
      ∂Measure.map initialHeterogeneousHistoryState (slowInitialPair n)) ≤ 0
    rw [lintegral_map (measurable_fst.comp measurable_fst)
      measurable_initialHeterogeneousHistoryState]
    simp [initialHeterogeneousHistoryState]
  · intro i
    by_cases hi : i < m
    · simpa only [slowCanonicalRetainedSeedTarget,
        if_pos (Nat.le_of_lt hi), if_pos hi,
        if_pos (by omega : i + 1 ≤ m), slowCanonicalRetainedError] using
        (slowCanonical_retained_phaseSeedTV hn m k hk hq4 heps heps1 hK hKc
          hball hfin slack boundSq hslack hbound scoreScale hi)
    · unfold slowCanonicalCostedActiveSchedule slowCanonicalRetainedError
      simp only [costedActiveReferenceTailSchedule,
        if_neg (by omega : ¬ i + 1 < m + 1)]
      rw [show slowCanonicalRetainedSeedTarget m n q K (i + 1) =
          slowRadiusQSeedTarget n q (slowSourceInitialVariance n) K (i + 1) by
        simp only [slowCanonicalRetainedSeedTarget,
          if_neg (by omega : ¬ i + 1 ≤ m)]]
      have heq :
          (slowCanonicalRetainedSeedTarget m n q K i).bind (Kernel.map
            (Kernel.const (State n)
              (Measure.map (fun z : ScoreSeed n ↦ ((0 : ENNReal), z))
                (slowStationaryTail n q (slowSourceInitialVariance n) K (i + 1))))
            (fun y : ENNReal × ScoreSeed n ↦ y.2.2)) =
          slowRadiusQSeedTarget n q (slowSourceInitialVariance n) K (i + 1) := by
        rw [Kernel.map_const _ (by fun_prop), Measure.const_comp, measure_univ, one_smul]
        unfold slowStationaryTail
        rw [Measure.map_map (by fun_prop) (by fun_prop),
          Measure.map_map (by fun_prop) (by fun_prop)]
        exact Measure.map_id
      rw [heq]
      simpa only [slowCanonicalRetainedError, if_neg hi] using
        (TVLe.refl (slowRadiusQSeedTarget n q (slowSourceInitialVariance n) K (i + 1)))
  · intro i
    by_cases hi : i < m
    · simpa only [slowCanonicalRetainedSeedTarget,
        if_pos (Nat.le_of_lt hi), if_pos hi,
        slowCanonicalRetainedCost] using
        (slowCanonical_retained_phaseCost hn m k hq4 hK hKc hball
          slack boundSq scoreScale hi)
    · unfold slowCanonicalCostedActiveSchedule slowCanonicalRetainedCost
      simp only [costedActiveReferenceTailSchedule, if_neg (by omega : ¬ i + 1 < m + 1)]
      rw [if_neg hi]
      change (∫⁻ _x, ∫⁻ y, y.1
        ∂Measure.map (fun z : ScoreSeed n ↦ ((0 : ENNReal), z))
          (slowStationaryTail n q (slowSourceInitialVariance n) K (i + 1))
        ∂slowCanonicalRetainedSeedTarget m n q K i) ≤ 0
      have hinner : (∫⁻ y, y.1
          ∂Measure.map (fun z : ScoreSeed n ↦ ((0 : ENNReal), z))
            (slowStationaryTail n q (slowSourceInitialVariance n) K (i + 1))) = 0 := by
        rw [lintegral_map]
        · simp
        · fun_prop
        · fun_prop
      simp [hinner]
  · exact hreadout
  · simpa only [zero_add] using herror
  · simpa only [zero_add] using hbudget
  · exact haccuracy

#print axioms exists_sourceReferenceTVOneRunCertificate_slowCanonical

end Ttc.CVSlowCanonicalSourceReferenceCertificate
